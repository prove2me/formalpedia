-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularChart_local
-- name    : ModularCurve.FullLevel.exists_supersingularChart_local
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/b4ce559f-fb5d-52d8-b7fe-f7b8dc3390b1
-- title:
--   Supersingular component chart with q+1 exceptional places
-- statement:
--   Fix a prime $q \ge 5$ and a nonzero natural number $M'$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$. Let $W$ be a finset of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places, i.e. the rational affine geometric places whose value at $\mathrm{jGeomGen}$ lies in $\mathrm{ssJSet}\,q$; let $\mathrm{hle}$ witness that the base-changed full-level field $\mathrm{modularFunctionFieldBar}\,M'$ sits inside $\mathrm{fieldBar}\,q\,M'$ (the base change to $\overline{\mathbb{Q}}$ of the $X_H$ function field of level $q^2M'$ for $H$ the kernel of reduction of units mod $q^2M'$ to units mod $q$); let $R_0$ be a `ConstantReduction` of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with reduced field $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$, i.e. a valuation subring $R_0.\mathrm{integers}$ with a surjective residue map onto that field with kernel the maximal ideal, compatible with $A$, together with a place map and the stated degree and divisor axioms; and assume $\mathrm{hR}_0$: for every Laurent series $y$ with coefficients in $A$ whose image in $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is the coefficientwise reduction of $y$. Let $s \in W$. Then there exist a field $\mathrm{FSS}$, an algebra structure on it over $\mathrm{ResidueField}\,A$, a `ComponentChart` $C$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ with reduced field $\mathrm{FSS}$, and a finset $N$ of places of $\mathrm{FSS}$ over $\mathrm{ResidueField}\,A$ such that: (i) $\mathrm{FSS}$ contains an element transcendental over $\mathrm{ResidueField}\,A$; (ii) $C$ lies over $s$, in the sense that for every $f \in R_0.\mathrm{integers}$ having nonnegative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the image of $\mathrm{jq}$ under the coefficient embedding has nonnegative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $C.\mathrm{integers}$ and its $C$-residue is the image in $\mathrm{FSS}$ of the value of $s$ at that $R_0$-residue; (iii) for every $\zeta \in \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M') \cap SL(2,\mathbb{Z})$, the pullback of $C$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ has the same subring of integers as $C$; (iv) $|N| = q+1$; and (v) for every place $Q$ of $\mathrm{FSS}$ with $Q \notin N$ there is $T \in C.\mathrm{integers}$ whose $C$-residue is nonzero of order $1$ at $Q$, such that every $P \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,P = Q$ satisfies $T \in P$'s valuation subring with $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and for each $c$ in the maximal ideal of $A$ there is exactly one such $P$ with $P.\mathrm{evalAt}\,T = c$; moreover each such $P$ has nonnegative order at the image in $\mathrm{fieldBar}\,q\,M'$ of the coefficient embedding of $\mathrm{jq}$.
--
--   This is the existence of a supersingular component in the semistable reduction of the full-level modular curve at a place above $q$: the chart $C$ reduces to the component over the chosen supersingular point $s$, it has $q+1$ distinguished (node) places, and each remaining reduced place has a fibre which is a full residue disc, parametrised by $T$ and containing no cusp. It is the local input to [`ModularCurve.FullLevel.exists_supersingularChart`](thm.html#ModularCurve.FullLevel.exists_supersingularChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularChart_local.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
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

theorem ModularCurve.FullLevel.exists_supersingularChart_local
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
    (s : ↥W) :
    ∃ (FSS : Type) (_ : Field FSS) (_ : Algebra (ResidueField A) FSS)
      (C : ComponentChart A (fieldBar q M') FSS) (N : Finset (Place (ResidueField A) FSS)),
      (∃ t : FSS, Transcendental (ResidueField A) t) ∧
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers,
            C.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))) ∧
      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).integers = C.integers) ∧

      N.card = q + 1 ∧
      (∀ Q : Place (ResidueField A) FSS, Q ∉ N →
        (∃ (T : ↥(fieldBar q M')) (hT : T ∈ C.integers), C.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (C.residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ C.dom, C.placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ C.dom ∧ C.placeMap P = Q ∧ P.evalAt T = c) ∧
        ∀ P ∈ C.dom, C.placeMap P = Q →
          0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M')) := by sorry
