-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_two_mul_placeWidthChar_mul_genusFF_add_of_chart_over
-- name    : ModularCurve.FullLevel.two_mul_placeWidthChar_mul_genusFF_add_of_chart_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/ad1d1bb8-b198-5963-8292-673d0b3be9f7
-- title:
--   Genus equation for a supersingular component chart
-- statement:
--   Fix a prime $q\ge 5$ and a nonzero natural number $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a nonunit of $A$; write $k=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,M'$ over $k$ whose members are exactly the supersingular places, i.e. those places $w$ that are rational (the map $k\to w$'s residue field is onto), satisfy `IsAffineGeomPlace`, and have $w.\mathrm{evalAt}$ of the generator `jGeomGen` lying in the set `ssJSet q` of supersingular $j$-invariants. Assume the base-changed full level-$M'$ modular function field $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ is contained in $\mathrm{fieldBar}\,q\,M'$, the function field over $\overline{\mathbb Q}$ of $X_H$ of level $q^2M'$ with $H$ the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$ (units congruent to $1$ modulo $q$). Let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with reduction field $\mathrm{modularFunctionFieldC}\,k\,M'$: a valuation subring of it with a surjective residue homomorphism whose kernel is the maximal ideal, inducing on $\overline{\mathbb Q}$ exactly $A$, together with a degree-preserving map on places compatible with divisors of functions. Assume further that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0$'s ring of integers and its $R_0$-residue is the coefficientwise reduction of $y$ modulo the maximal ideal of $A$. Let $s\in W$, let $\bar F$ be a field that is a $k$-algebra, and let $C$ be a component chart of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduction field $\bar F$. Assume: (h0) $\bar F$ contains an element transcendental over $k$; (h1) whenever $f$ lies in $R_0$'s integers, is regular at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the element $j$ (the coefficientwise image of `jq`) is regular, and has $R_0$-residue in the valuation subring of $s$, then the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $C$'s integers and its $C$-residue is the image in $\bar F$ of the value at $s$ of that $R_0$-residue; (h2) for every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb Q}$ and every $\gamma\in\mathrm{SL}_2(\mathbb Z)$ with $\gamma\in\Gamma_0(M')$, the pullback of $C$'s integers along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ equals $C$'s integers. Then, with $e=\mathrm{placeWidthChar}\,q\,M'\,s$, namely `jWidthChar q` of the value of `jGeomGen` at $s$ (for $q\ge5$ this is `jWidth` of that value) divided by $\mathrm{placeRamificationJ}\,M'\,s$, the order at $s$ of $j-j(s)$, and with $g=\mathrm{genusFF}\,k\,\bar F$ the $k$-dimension of $H^1$ of the zero divisor, one has $$2e\,(2g+q)+1=q^2+2e.$$
--
--   This is the genus computation for the component of the special fibre of the modular curve sitting above a supersingular point: the reduced field $\bar F$ of the chart is the function field of a quotient of the Deligne–Lusztig (Drinfeld) curve $xy^q-x^qy=1$ by a group of order $2e$, and the displayed identity is the resulting genus equation, equivalently $2e(2g+q-1)=q^2-1$. It feeds the computation of the genus of $\mathrm{fieldBar}\,q\,M'$ from the Igusa model together with the supersingular charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_two_mul_placeWidthChar_mul_genusFF_add_of_chart_over.lean

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

theorem ModularCurve.FullLevel.two_mul_placeWidthChar_mul_genusFF_add_of_chart_over
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
