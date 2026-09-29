-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_quotField_of_chart_over_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/8d555e99-450e-5d4e-a481-b5895b6a17f6
-- title:
--   Supersingular component charts as Drinfeld-curve quotients, q=2
-- statement:
--   Fix a prime $q$ together with the hypothesis $q = 2$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, write $\kappa =$ `ResidueField A`, and let $W$ be a finite set of places of `modularFunctionFieldC` $\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places, i.e. those $w$ that are rational, affine geometric, and satisfy $w(\,j\,) \in$ `ssJSet q` for the geometric $j$-generator. Assume the inclusion `hle` of `modularFunctionFieldBar M'` in `fieldBar q M'` inside the Laurent series over $\overline{\mathbb{Q}}$, and let $R_0$ be a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC` $\kappa\,M'$ which, by `hR₀`, reduces every Laurent series with coefficients in $A$ lying in `modularFunctionFieldBar M'` coefficientwise modulo the maximal ideal of $A$. Let $s \in W$, let $\bar F$ be a field that is a $\kappa$-algebra, and let $C$ be a `ComponentChart` of $A$ on `fieldBar q M'` with values in $\bar F$, subject to: $\bar F$ contains an element transcendental over $\kappa$; `h1`, that every $f$ in $R_0$'s valuation subring which is regular at each place of `modularFunctionFieldBar M'` where the image of `jq` is regular and whose $R_0$-residue lies in the valuation subring of $s$, has its image in `fieldBar q M'` inside `C.integers`, with $C$-residue the image in $\bar F$ of the value at $s$ of that $R_0$-residue; and `h2`, that for every primitive $q$-th root of unity index $\zeta$ and every $\gamma \in \Gamma_0(M')$ the pullback of $C$ along `levelAutBar q M' ζ γ` has the same ring of integers as $C$. Assume further a $\mathbb{F}_{q^2}$-algebra structure on $\kappa$ and that the Drinfeld coordinate ring `CoordRing q` $\kappa$ is a domain. Then there is a subgroup $C_s$ of the group of $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ with $\#C_s =$ `placeWidthChar q M' s` (the char-$q$ $j$-width at $s$ divided by the ramification of $j$ at $s$), and $\bar F$ is isomorphic as a $\kappa$-algebra to [`DrinfeldCurve.quotField q`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) $\kappa\,C_s$, the fixed field of the scalar action of $C_s$ on the Drinfeld function field over $\kappa$.
--
--   This is the identification, in residue characteristic $2$ and with the rigidifying auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing the level $M'$, of the component of the semistable reduction of the full-level modular curve lying over a supersingular point $s$ of $X_0(M')$ with a quotient of the Drinfeld curve $xy^q - x^q y = 1$ by a group of scalars, the order of the scalar group being exactly the width `placeWidthChar q M' s`. It feeds the genus and width computation [`ModularCurve.FullLevel.placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_two_of_dvd) for these charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_quotField_of_chart_over_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup DrinfeldCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
    (h2 : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).integers = C.integers)
    (inst : Algebra (GaloisField q 2) (ResidueField A)) [IsDomain (DrinfeldCurve.CoordRing q (ResidueField A))] :
    ∃ Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)),
      Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
      Nonempty (Fbar ≃ₐ[ResidueField A] ↥(DrinfeldCurve.quotField q (ResidueField A) Cs)) := by sorry
