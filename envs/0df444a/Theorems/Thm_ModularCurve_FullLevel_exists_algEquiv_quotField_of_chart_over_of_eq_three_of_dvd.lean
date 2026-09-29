-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_quotField_of_chart_over_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/d52a6ca9-8f53-5356-8fa6-7b8e12be44b5
-- title:
--   Supersingular chart is a Drinfeld quotient field, q=3
-- statement:
--   Fix a prime $q$ with $q=3$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, write $\kappa =$ `ResidueField A`, and let $W$ be a finite set of places of $\kappa$-algebra `modularFunctionFieldC` $\kappa\,M'$ consisting exactly of the places lying in `ssPlaces q M'`$\kappa$, i.e. those $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathtt{jGeomGen})\in$ `ssJSet q`$\kappa$. Assume the $\overline{\mathbb{Q}}$-base change `modularFunctionFieldBar M'` of the full level-$M'$ modular function field is contained in `fieldBar q M'`, the $\overline{\mathbb{Q}}$-function field of $X_H$ of level $q^2M'$ for $H$ the kernel of $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` with values in `modularFunctionFieldC`$\kappa\,M'$ (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map with kernel the maximal ideal, a map on places preserving degrees, and the stated compatibilities), and assume $R_0$ computes coefficientwise reduction: for every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0.\mathrm{integers}$ and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Let $s \in W$, let $\bar F$ be a field that is an algebra over $\kappa$, and let $C$ be a component chart of `fieldBar q M'` over $A$ with values in $\bar F$. Assume: $\bar F$ contains an element transcendental over $\kappa$; $C$ lies over $s$ through $R_0$, in the sense that every $f \in R_0.\mathrm{integers}$ which has non-negative order at every place of `modularFunctionFieldBar M'` where the $q$-expansion $j$ of the modular invariant has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, has image in $C.\mathrm{integers}$ with $C$-residue the image in $\bar F$ of the value at $s$ of the $R_0$-residue of $f$; and $C.\mathrm{integers}$ is invariant under pullback along `levelAutBar q M'` $\zeta\,\gamma$ for every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$ and every $\gamma \in \Gamma_0(M')$. Finally let $\kappa$ carry an algebra structure over $\mathbb{F}_{q^2}$ for which the Drinfeld coordinate ring `CoordRing q`$\kappa$ is a domain. Then there is a subgroup $C_s$ of $\mu_{q+1}(\mathbb{F}_{q^2})$ with $\#C_s = 2\cdot$ `placeWidthChar q M'` $s$ such that $\bar F$ is isomorphic, as a $\kappa$-algebra, to the fixed field [`DrinfeldCurve.quotField q`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32)$\kappa\,C_s$ of the scalar action of $C_s$ on the function field of the Drinfeld curve over $\kappa$.
--
--   This identifies a component of the special fibre at $q$ of the semistable model of the modular curve of level $K(q)K_0(M')$, cut out by a level-stable component chart lying over a supersingular point $s$ of $X_0(M')_{\kappa}$, with the quotient of the Drinfeld curve $xy^q - x^qy = 1$ by a group of scalars of order twice the width of $s$; it is the $q=3$ analogue, at a rigid auxiliary level given by $\ell$, of the corresponding statement for $q \ge 5$. It feeds the genus computation [`ModularCurve.FullLevel.two_mul_placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.two_mul_placeWidthChar_mul_genusFF_add_of_chart_over_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_quotField_of_chart_over_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_three_of_dvd
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
    (h2 : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).integers = C.integers)
    (inst : Algebra (GaloisField q 2) (ResidueField A)) [IsDomain (DrinfeldCurve.CoordRing q (ResidueField A))] :
    ∃ Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)),
      Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
      Nonempty (Fbar ≃ₐ[ResidueField A] ↥(DrinfeldCurve.quotField q (ResidueField A) Cs)) := by sorry
