-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings
-- name    : ModularCurve.FullLevel.exists_igusaValuationSubrings
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/cd428653-9c80-5dfa-8692-2fc5673013cd
-- title:
--   Existence of the Igusa valuation rings at full level q
-- statement:
--   Let $q\ge 5$ be a prime, let $M'$ be a non-zero natural number with $q \nmid M'$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$, and let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$. Write $\kappa$ for the residue field of $A$, $H \le (\mathbb{Z}/q^2M')^\times$ for the kernel of reduction to $(\mathbb{Z}/q)^\times$, and $F =$ `fieldBar q M'` for the compositum of $\overline{\mathbb{Q}}$ with the function field of level $\Gamma_H(q^2M')$ inside $\overline{\mathbb{Q}}((q))$. Then there are a family of valuation subrings $\mathcal{O}_\ell \subseteq F$ indexed by the lines $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$ and a regular prolongation $R$ of $A$ from $\overline{\mathbb{Q}}$ to $F$ with residue field the $q$-expansion function field of level $\Gamma_H(q^2M')$ over $\kappa$ (so $R$ consists of a valuation subring of $F$ whose intersection with $\overline{\mathbb{Q}}$ is $A$, together with a surjective residue map onto that $q$-expansion field whose kernel is the maximal ideal, compatible with reduction on $A$), such that: the integers of $R$ are $\mathcal{O}_{[1:0]}$; an element $f \in F$ lies in $\mathcal{O}_{[1:0]}$ exactly when $f \cdot y = x$ for some Laurent series $x,y$ with coefficients in $A$, pushed into $\overline{\mathbb{Q}}((q))$ coefficientwise, with the coefficientwise reduction of $y$ to $\kappa((q))$ non-zero; every Laurent series over $A$ whose image lies in $F$ belongs to the integers of $R$, with residue equal to its coefficientwise reduction; for each $\ell$ there is $\gamma \in \Gamma_0(M')$ whose reduction modulo $q$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ sends $[1:0]$ to $\ell$ and for which $\mathcal{O}_\ell$ is the preimage of $\mathcal{O}_{[1:0]}$ under the level automorphism `levelAutBar q M' ζ γ` of $F$ over $\overline{\mathbb{Q}}$; the map $\ell \mapsto \mathcal{O}_\ell$ is injective; and for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ there is a permutation $\sigma$ of $\mathbb{P}^1(\mathbb{Z}/q)$ with $\mathcal{O}_\ell$ pulled back along `levelAutBar q M' ζ' γ` equal to $\mathcal{O}_{\sigma \ell}$.
--
--   This is the function-field form of the statement that the semistable model of $X(\Gamma(q)\cap\Gamma_0(M'))$ over $A$ has $q+1$ Igusa components, labelled by the lines of $\mathbb{P}^1(\mathbb{F}_q)$, with the Gauss point of the $q$-expansion prolongation sitting at $[1:0]$ and $\Gamma_0(M')$ permuting the components through its reduction modulo $q$. It is used in the construction of the semistable covering of the full-level modular curve at $q$, in particular by the results producing regular prolongations whose integers are the Igusa–Gauss ring and by the uniqueness statement for such rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings.lean

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

theorem ModularCurve.FullLevel.exists_igusaValuationSubrings
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
