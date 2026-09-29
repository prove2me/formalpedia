-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_two
-- name    : ModularCurve.FullLevel.exists_igusaValuationSubrings_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/4922d8ab-54bd-5cc2-a3e8-fc12d6ca320b
-- title:
--   Igusa valuation subrings at full level for q = 2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M' \ge 1$ with $q \nmid M'$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ lying in its set of non-units (so $A$ lies over $q$), write $\kappa$ for its residue field, and fix a primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$. Put $F = \mathrm{fieldBar}\,q\,M'$, the $\overline{\mathbb{Q}}$-base change inside $\overline{\mathbb{Q}}((Q))$ of the function field of level $\Gamma_H(q^2M')$, where $H = \mathrm{levelH}\,q\,M'$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ mod $q$. The assertion is that there exist a family $\mathcal{O}_\ell$ of valuation subrings of $F$ indexed by $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$ and a regular prolongation $R$ of $A$ from $\overline{\mathbb{Q}}$ to $F$ with residue field the $q$-expansion function field `xHFunctionFieldC` of the same level over $\kappa$ — that is, a valuation subring $R.\mathrm{integers}$ of $F$ contracting to $A$, together with a surjective ring map to that $q$-expansion field whose kernel is the maximal ideal, compatible with reduction on $A$ and satisfying the scaling condition of `RegularProlongation` — such that: (i) $R.\mathrm{integers} = \mathcal{O}_{[1:0]}$; (ii) for $f \in F$ one has $f \in \mathcal{O}_{[1:0]}$ if and only if $f \cdot \iota(y) = \iota(x)$ for some Laurent series $x, y$ over $A$ whose coefficientwise reduction satisfies $\bar y \ne 0$, where $\iota$ is coefficientwise inclusion $A((Q)) \to \overline{\mathbb{Q}}((Q))$; (iii) every element of $F$ of the form $\iota(y)$ with $y$ a Laurent series over $A$ lies in $R.\mathrm{integers}$ and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; (iv) for each $\ell$ there is $\gamma \in \Gamma_0(M')$ with $\mathrm{redQ}\,q\,\gamma \cdot [1:0] = \ell$ and $\mathcal{O}_\ell$ the preimage of $\mathcal{O}_{[1:0]}$ under the level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ of $F$; (v) $\ell \mapsto \mathcal{O}_\ell$ is injective; and (vi) for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$, pulling back along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permutes the family, i.e. agrees with $\mathcal{O}_{\sigma(\cdot)}$ for some permutation $\sigma$ of $\mathbb{P}^1(\mathbb{Z}/q)$.
--
--   This is the $q = 2$ case of the construction of the Igusa valuation rings attached to the components of the reduction modulo $q$ of the modular curve of level $\Gamma_H(q^2M')$, the Gauss $q$-expansion ring $\mathcal{O}_{[1:0]}$ and its translates under $\Gamma_0(M')$ acting through $\mathrm{SL}_2(\mathbb{F}_q)$ on $\mathbb{P}^1(\mathbb{F}_q)$. It supplies the charts used by the downstream constructions of semistable models and of the specialisation of the Jacobian at $q = 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_igusaValuationSubrings_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q) :
    ∃ (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
      (R : RegularProlongation A (fieldBar q M')
        (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),

      R.integers = OIg (lineInfty q) ∧
      (∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
              LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y) ∧

      (∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
        OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom) ∧

      Function.Injective OIg ∧

      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
          ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ)) := by sorry
