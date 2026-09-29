-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_two_mul_placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.two_mul_placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/c8eb92c6-609d-545a-ac7d-21db6fb82b12
-- title:
--   Genus of a supersingular component chart at q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, and write $k=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,M'$ over $k$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,M'\,k$, i.e. the places $w$ that are rational, affine geometric, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,k\,M')\in \mathrm{ssJSet}\,q\,k$. Assume an inclusion $\mathrm{hle}$ of $\mathrm{modularFunctionFieldBar}\,M'$, the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field, into $\mathrm{fieldBar}\,q\,M'$, the base change of the $X_H$-function field for $H=\mathrm{levelH}\,q\,M'$ inside $q^2M'$. Let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with reduced field $\mathrm{modularFunctionFieldC}\,k\,M'$, compatible with coefficientwise reduction in the sense that for every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $k$, is the coefficientwise reduction of $y$. Fix $s\in W$, a field $Fbar$ over $k$, and a component chart $C$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduced field $Fbar$, subject to: ($h_0$) some element of $Fbar$ is transcendental over $k$; ($h_1$) for every $f\in R_0.\mathrm{integers}$ that has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which $j_q$ has non-negative order, and whose $R_0$-residue lies in the valuation ring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $C.\mathrm{integers}$ and its $C$-residue is the image in $Fbar$ of the value at $s$ of that $R_0$-residue; ($h_2$) for every $\zeta\in\mathrm{Idx}\,q$, a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and every $\gamma\in SL(2,\mathbb{Z})$ lying in $\Gamma_0(M')$, the chart obtained by pulling $C$ back along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ has the same ring of integers as $C$. Then, writing $e=\mathrm{placeWidthChar}\,q\,M'\,s$, i.e. $6$ or $1$ according as the $j$-value of $s$ vanishes or not, divided by the ramification index of $s$ over the $j$-line, and $g=\mathrm{genusFF}\,k\,Fbar$, one has $2e(2g+q)+1=q^2+2e$, equivalently $2e(2g+q-1)=q^2-1$.
--
--   This is the genus computation for the supersingular components of the special fibre at $3$ of the modular curve of level $q^2M'$: each such component, presented by the chart $C$, is a quotient of the Drinfeld (Hermitian) curve $y^q-y=x^{q+1}$ over $k$ by a subgroup of the $(q+1)$-st roots of unity of order $2e$, and the displayed identity is the resulting relation between the genus, $q$ and the width $e$. It feeds the computation of the genus of $\mathrm{fieldBar}\,q\,M'$ in [`ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_two_mul_placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.two_mul_placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W) (Fbar : Type) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A (fieldBar q M') Fbar)
    (h0 : ∃ t : Fbar, Transcendental (ResidueField A) t)
    (h1 :
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers,
            C.residue ⟨_, hC⟩ = algebraMap (ResidueField A) Fbar
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).integers = C.integers) :
    2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) *
        (2 * AlgebraicCurve.genusFF (ResidueField A) Fbar + q) + 1 =
      q ^ 2 + 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) := by sorry
