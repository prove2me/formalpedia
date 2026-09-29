-- Prove2me | Theorems.Thm_ModularCurve_ComponentChart_residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar
-- name    : ModularCurve.ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b3c9832e-a099-53b1-a3fb-68c4cd2bd1dc
-- title:
--   Vanishing of the Fricke transform at a supersingular node
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (the predicate `LiesOverPrime`), and assume its residue field $k$ is algebraically closed of characteristic $p$. Let $C$ be a component chart for $A$ of the geometric modular function field $F=\overline{\mathbb{Q}}\cdot\mathcal{F}_{1\cdot p}$ inside $\overline{\mathbb{Q}}((q))$, with residue field the rational line $k(\tilde\jmath)=\,$`modularFunctionFieldC k 1`; so $C$ consists of a valuation subring `C.integers` of $F$, a surjective ring map `C.residue` onto that line with kernel the maximal ideal, a domain `C.dom` of places of $F$, a finite set `C.nodes` of places of the line, and a place map, subject to the compatibilities in `ComponentChart`. Assume: `C.integers` is exactly the set of $g$ whose Laurent expansion lies in `CharPReduction.modularLocalized (1 * p) A (residue A)`; for such $g$ the image under `C.residue`, read in $k((q))$, is the coefficientwise reduction `CharPReduction.modularRedLocHom (1 * p) A (residue A)`; the nodes of $C$ are precisely the places $\tilde\jmath=a$ of the line with $a$ in `ssJSet p k`, i.e. such that every elliptic curve over $k$ with $j$-invariant $a$ has no nonzero $p$-torsion point; and the cusp $\bar 0 =w_p\bar\infty$ does not lie in `C.dom`. Let $f\neq 0$ in $F$ be such that every place $W$ with $W.\mathrm{ord}\,f<0$ equals `cuspInftyBar (1 * p)`, and suppose both $f$ and $w_pf=\,$`frickeInvolutionBar (1 * p) f` lie in `C.integers`. If $a\in$ `ssJSet p k` and the place $\tilde\jmath=a$ takes the value $0$ at the residue of $f$ (that residue lies in the valuation ring of that place and reduces to $0$ there), then the residue of $w_pf$ is $0$.
--
--   This records the geometric input coming from the two components $V_\infty$ and $V_0$ of the special fibre of $X_0(p)$ at $p$, which are exchanged by the Fricke involution $w_p$ and meet at the supersingular points: a function with poles only at $\bar\infty$ whose reduction along $V_\infty$ vanishes at a supersingular crossing cannot have a nonzero reduction along the transported chart attached to $V_0$. It is used in the construction and estimates for families of functions on the multiplicative covering, notably in the lemmas on the zero chart and on the Hasse exponent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComponentChart_residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar
    {p : ℕ} [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (C : ComponentChart A (modularFunctionFieldBar (1 * p))
      ↥(modularFunctionFieldC (ResidueField ↥A) 1))
    (hint_iff : ∀ g : modularFunctionFieldBar (1 * p), g ∈ C.integers ↔
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
    (hres : ∀ (g : modularFunctionFieldBar (1 * p))
      (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
      ∃ h : g ∈ C.integers,
        ((C.residue ⟨g, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A))
          = CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, hg⟩)
    (hnodes : ∀ x, x ∈ C.nodes ↔ ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = x)
    (hzero_not : cuspZeroBar (1 * p) ∉ C.dom)
    (f : modularFunctionFieldBar (1 * p)) (hf0 : f ≠ 0)
    (hfpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord f < 0 → W = cuspInftyBar (1 * p))
    (hf_int : f ∈ C.integers)
    (hwf_int : frickeInvolutionBar (1 * p) f ∈ C.integers)
    (a : ResidueField ↥A) (ha : a ∈ ssJSet p (ResidueField ↥A))
    (hval : (charLGeomPlaceOfPoint (ResidueField ↥A) a).HasValue (C.residue ⟨f, hf_int⟩) 0) :
    C.residue ⟨frickeInvolutionBar (1 * p) f, hwf_int⟩ = 0 := by sorry
