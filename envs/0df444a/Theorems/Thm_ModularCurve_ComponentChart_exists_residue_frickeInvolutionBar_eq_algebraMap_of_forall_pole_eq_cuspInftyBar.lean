-- Prove2me | Theorems.Thm_ModularCurve_ComponentChart_exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar
-- name    : ModularCurve.ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b1ce1614-dd65-5606-91c4-dd4b478fb3ee
-- title:
--   Fricke image of a pole-free unit reduces to a nonzero constant
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, meaning that $p$ is a nonunit of $A$, whose residue field $k$ is of characteristic $p$ and algebraically closed. Let $C$ be a component chart for $A$ on the field $F =$ `modularFunctionFieldBar (1 * p)` (the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot p$ inside Laurent series) with residue field target the subfield `modularFunctionFieldC k 1` of $k((q))$ generated over $k$ by $j$ and $j$ at level $1$; thus $C$ consists of a valuation subring $C.\mathrm{integers}$ of $F$, a surjective ring homomorphism $C.\mathrm{residue}$ onto that subfield with kernel the maximal ideal and compatible with the residue map of $A$, a set $C.\mathrm{dom}$ of places of $F$ over $\overline{\mathbb{Q}}$, a finite set $C.\mathrm{nodes}$ of places of the residue line over $k$, a map $C.\mathrm{placeMap}$ on places, and the chart axioms (scaling to a nonzero residue, avoidance of nodes on the domain, the pointwise value law, and compatibility with divisors away from the nodes). Assume in addition that the chart is the Gauss chart at the $q$-expansion cusp: a function $g$ of $F$ lies in $C.\mathrm{integers}$ exactly when its $q$-expansion lies in the localised ring `CharPReduction.modularLocalized (1 * p) A red` of $A$-integral expansions, and for every such $g$ the element $C.\mathrm{residue}(g)$ is, as a Laurent series over $k$, the coefficientwise reduction `CharPReduction.modularRedLocHom (1 * p) A red` of its $q$-expansion; that the nodes of $C$ are exactly the places $\mathrm{charLGeomPlaceOfPoint}\,k\,a$ for $a$ in $\mathrm{ssJSet}\,p\,k$, i.e. those $a \in k$ such that every elliptic curve over $k$ with $j$-invariant $a$ has no nonzero $p$-torsion point; and that the place `cuspZeroBar (1 * p)`, the image of the $q$-expansion cusp under the Fricke involution, does not lie in $C.\mathrm{dom}$. Let $f \neq 0$ in $F$ be such that every place $W$ with $W.\mathrm{ord}\,f < 0$ equals `cuspInftyBar (1 * p)`, let $f$ and its Fricke image $w_p f$ both lie in $C.\mathrm{integers}$, and let the residue $C.\mathrm{residue}(w_p f)$ be nonzero. Then there is $c_0 \in k$, $c_0 \neq 0$, with $C.\mathrm{residue}(w_p f)$ equal to the image of $c_0$ under the structure map $k \to$ `modularFunctionFieldC k 1`.
--
--   This is the statement that on the special fibre of $X_0(p)$ at $p$, a function with poles only at the cusp $\infty$ which is integral along the second component and has nonzero reduction there restricts on that component to a nonzero constant: having no poles on a genus-zero line, away from the supersingular crossings by the divisor-compatibility of the chart and at the crossings by the node value law, it must be constant. It is used in the multiplicative-covering estimates of the project, for instance in the lemmas on Hasse exponents and on membership in the integers of the chart at the zero cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComponentChart_exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar.lean

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

theorem ModularCurve.ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar
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
    (hwf_res : C.residue ⟨frickeInvolutionBar (1 * p) f, hwf_int⟩ ≠ 0) :
    ∃ c₀ : ResidueField ↥A, c₀ ≠ 0 ∧
      C.residue ⟨frickeInvolutionBar (1 * p) f, hwf_int⟩
        = algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c₀ := by sorry
