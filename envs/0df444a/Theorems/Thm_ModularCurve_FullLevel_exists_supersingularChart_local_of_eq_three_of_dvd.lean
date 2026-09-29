-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularChart_local_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularChart_local_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/1518e45b-b31a-54d0-94a0-5e4744cdfa95
-- title:
--   Local supersingular chart at q=3 with q+1 exceptional places
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places (those places that are rational, affine geometric, and take the generator $\mathrm{jGeomGen}$ into the supersingular $j$-set for $q$), let $hle$ witness $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ which, by the hypothesis $hR_0$, sends every Laurent series with coefficients in $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$ into its ring of integers and computes its residue by reducing coefficients modulo the maximal ideal of $A$. Fix $s\in W$. Then there are a field $FSS$ which is an algebra over $\mathrm{ResidueField}\,A$, a component chart $C$ of $\mathrm{fieldBar}\,q\,M'$ relative to $A$ with reduction into $FSS$, and a finite set $N$ of places of $FSS$ over $\mathrm{ResidueField}\,A$, such that: $FSS$ contains an element transcendental over $\mathrm{ResidueField}\,A$; for every $f$ in the ring of integers of $R_0$ which has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the coefficientwise image of the Laurent expansion $\mathrm{jq}$ of $j$ has non-negative order, and whose $R_0$-residue lies in the valuation ring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $C$'s ring of integers and its $C$-residue is the image under $\mathrm{ResidueField}\,A\to FSS$ of the value of $s$ at the $R_0$-residue of $f$; for every primitive $q$-th root of unity $\zeta$ (an element of $\mathrm{Idx}\,q$) and every $\gamma\in\Gamma_0(M')\subset \mathrm{SL}_2(\mathbb{Z})$, the chart obtained by pulling $C$ back along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ has the same ring of integers as $C$; $N$ has exactly $q+1$ elements; and for every place $Q$ of $FSS$ over $\mathrm{ResidueField}\,A$ with $Q\notin N$ there is $T$ in $C$'s ring of integers whose $C$-residue is non-zero and has order $1$ at $Q$, such that every $P\in C.\mathrm{dom}$ specialising to $Q$ has $T$ in its valuation ring with value lying in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is exactly one place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ with $P\in C.\mathrm{dom}$, specialising to $Q$, and with $P$-value of $T$ equal to $c$; moreover every $P\in C.\mathrm{dom}$ specialising to $Q$ has non-negative order at the image in $\mathrm{fieldBar}\,q\,M'$ of the coefficientwise image of $\mathrm{jq}$.
--
--   This is the local form, at the prime $q=3$, of the supersingular component of the semistable model of the full-level modular curve: a chart of the base-changed function field of $X_H(q^2M')$ over the valuation ring $A$ whose reduction is a supersingular component carrying $q+1$ distinguished places, all remaining reduced places having open-disc fibres free of cusps, with the chart stable under the level automorphisms indexed by $\mathrm{Idx}\,q$ and $\Gamma_0(M')$. It feeds the globalisation statement [`ModularCurve.FullLevel.exists_supersingularChart_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularChart_of_eq_three_of_dvd); the auxiliary prime $\ell\equiv 11\pmod{12}$ dividing $M'$ serves to rigidify the level at the characteristic-$3$ supersingular point with extra automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularChart_local_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_supersingularChart_local_of_eq_three_of_dvd
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
