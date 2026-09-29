-- Prove2me | Theorems.Thm_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne
-- name    : ModularCurve.exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/ad6f0ae8-b14c-5a62-bb80-b4d9e9ab1d31
-- title:
--   Wide supersingular annuli of X₀(p) attached to both charts
-- statement:
--   Let $p\ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k=\mathrm{ResidueField}(A)$ has characteristic $p$ and is algebraically closed, and write $F=\mathtt{modularFunctionFieldBar}\,(1\cdot p)$ for the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot p$ inside Laurent series. Let $C_0$, resp. $C_i$, be component charts of $F$ along $A$ with residue fields $\bar F_0$, resp. $\bar F_i$, extensions of $k$, and let $x_0\in C_0.\mathrm{nodes}$, $x_i\in C_i.\mathrm{nodes}$ be places of those residue fields over $k$. Let $a\in k$ lie in $\mathtt{ssJSet}\,p\,k$, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no non-zero point killed by $p$, and assume $a^{p^2}=a$ and $a=0$ or $a=1728$. Four dictionary hypotheses relate the charts to reductions of the localised modular ring $\mathtt{modularLocalized}\,(1\cdot p)$ for $A$ and the residue map, via $\mathtt{modularRedLocHom}$: every $g\in F$ whose Fricke transform $\mathtt{frickeInvolutionBar}\,(1\cdot p)\,g$, resp. $g$ itself, lies in the localised ring with non-zero reduction belongs to $C_0.\mathrm{integers}$, resp. $C_i.\mathrm{integers}$, with non-zero chart residue; and for such $g$ with reduction lying in the level-one modular function field $\mathtt{modularFunctionFieldC}\,k\,1$, the order at $x_0$, resp. $x_i$, of the chart residue equals the order of that reduction at the place $\mathtt{charLGeomPlaceOfPoint}\,k\,(a^p)$, resp. at $\mathtt{charLGeomPlaceOfPoint}\,k\,a$. The conclusion asserts the existence of two annuli $\mathrm{An}$, $\mathrm{An}'$ of $F$ along $A$ with the same domain and the same modulus, with the modulus non-zero in $\overline{\mathbb Q}$, with $\mathrm{An}'.\mathrm{param}\cdot\mathrm{An}.\mathrm{param}$ equal to the image of that modulus under $\overline{\mathbb Q}\to F$, such that $\mathrm{An}$ is attached to $(C_0,x_0)$ and $\mathrm{An}'$ to $(C_i,x_i)$ — that is, the respective parameter lies in the chart's integers with residue of order $1$ at the node, and every chart integer with non-zero residue and order $0$ throughout the annulus domain satisfies the unit condition of $\mathtt{IsAttached}$ — such that a place $W$ of $F$ over $\overline{\mathbb Q}$ lies in $\mathrm{An}.\mathrm{dom}$ exactly when there are $x,y\in A$ with residues $a$ and $a^p$ and $W.\mathrm{ord}(j-x)>0$ and $W.\mathrm{ord}(j_p-y)>0$, where $j$ is the $q$-expansion $\mathtt{jq}$ in $F$ and $j_p$ its image under $\mathtt{qExpand}\,\mathbb Q\,(1\cdot p)$, and finally such that $\mathrm{An}.\mathrm{modulus}=p^{\mathtt{jWidth}\,a}$ in $A$, where $\mathtt{jWidth}\,a$ is $3$ for $a=0$ and $2$ for $a=1728$.
--
--   This is the supersingular edge of the semistable covering of $X_0(p)$ at a node of width greater than one, i.e. at a supersingular $j$-invariant with extra automorphisms, where the local equation is $xy=p^{e}$ with $e=3$ or $2$ rather than $e=1$; the statement records not merely the existence of the annulus pair but its attachment data at both ends and its precise domain and modulus. It is used in assembling the covering contexts and the prolongation data for component charts and annuli over a place specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type}
    [Field Fbar0]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    {Fbari : Type}
    [Field Fbari]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (hnodes0 : x0 ∈ C0.nodes)
    (hnodesi : xi ∈ Ci.nodes)
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        x0.ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)))
    (huniti : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 →
        ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * p))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      An.IsAttached C0 x0 ∧ An'.IsAttached Ci xi ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ))))) ∧
      An.modulus = ((p : ℕ) : ↥A) ^ jWidth a := by sorry
