-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_three
-- name    : ModularCurve.FullLevel.exists_igusaValuationSubrings_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/8add4907-0a01-5332-b9b4-388cf17a35dc
-- title:
--   Igusa valuation rings at q = 3 for full level
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M' \ge 1$ be an integer not divisible by $q$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$, viewed in $\overline{\mathbb{Q}}$, is a non-unit of $A$, and fix $\zeta$ a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$. Write $\bar F =$ `fieldBar q M'` for the compositum of $\overline{\mathbb{Q}}$ with the function field of level $\Gamma_H(q^2M')$ inside $\overline{\mathbb{Q}}((q))$, where $H =$ `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, and let $\kappa =$ `ResidueField A`. Then there exist a family $\mathcal{O}$ of valuation subrings of $\bar F$ indexed by the projective line $\mathbb{P}^1(\mathbb{Z}/q)$ and a regular prolongation $R$ of $A$ to $\bar F$ with residue target the $q$-expansion function field `xHFunctionFieldC` of level $\Gamma_H(q^2M')$ over $\kappa$ — that is, a valuation subring $R.\mathrm{integers}$ of $\bar F$ together with a surjective ring homomorphism onto that field whose kernel is the maximal ideal, inducing $A$ on $\overline{\mathbb{Q}}$ and compatible with the residue map of $A$, and such that every nonzero $f$ has a scalar multiple in $R.\mathrm{integers}$ with nonzero residue — satisfying all of the following. First, $R.\mathrm{integers} = \mathcal{O}([1:0])$, where $[1:0]$ is `lineInfty q`. Second, $f \in \mathcal{O}([1:0])$ if and only if there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f$ times the image of $y$ in $\overline{\mathbb{Q}}((q))$ equal to the image of $x$. Third, for every Laurent series $y$ over $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in $\bar F$, that element belongs to $R.\mathrm{integers}$ and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Fourth, for each $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$ there is $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$ whose reduction mod $q$ carries $[1:0]$ to $\ell$ and for which $\mathcal{O}(\ell)$ is the preimage of $\mathcal{O}([1:0])$ under the $\overline{\mathbb{Q}}$-algebra automorphism `levelAutBar q M' ζ γ` of $\bar F$ (the automorphism selected by the $q$-expansion compatibility condition `IsLevelAutBar` relative to $\zeta$ and $\gamma$, the identity if none exists). Fifth, the indexing is injective. Sixth, for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ there is a permutation $\sigma$ of $\mathbb{P}^1(\mathbb{Z}/q)$ with $\mathcal{O}(\ell)$ pulled back along `levelAutBar q M' ζ' γ` equal to $\mathcal{O}(\sigma(\ell))$ for all $\ell$.
--
--   This produces the Igusa components of the mod $q$ fibre of the full-level modular curve at $q = 3$: the $q$-expansion (Gauss) valuation ring together with its $\Gamma_0(M')$-translates, indexed faithfully and permuted by the level automorphisms. It is the $q = 3$ case of the construction used downstream to identify the integers of a regular prolongation with the Igusa–Gauss ring and to compare residues on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_igusaValuationSubrings_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
