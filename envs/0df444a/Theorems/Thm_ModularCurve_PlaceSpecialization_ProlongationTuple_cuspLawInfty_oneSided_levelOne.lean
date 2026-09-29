-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/534abd83-02f3-5b17-bb45-6a01aed7d989
-- title:
--   One-sided cusp law at infinity, auxiliary level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be a `ModularPolynomialData` for $q$, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence that the mod-$q$ reduction of $\Phi$ equals $(X^q - Y)(X - Y^q)$, and let `hα`, `hβ` assert that the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ from level $1$ to level $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Given a place specialization $P$ of these data and a prolongation tuple $R$ over $P$ which satisfies `R.IsModel`, that is, the conjunction of the two divisor laws and the two cusp laws at infinity and at zero, the assertion is the following. Let $f$ be an element of `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot q$ inside $\overline{\mathbb{Q}}$-Laurent series, lying in the integers of the first regular prolongation $R.R_1$ and with non-zero residue there. Let $D$ be a divisor on that field, i.e. a finitely supported integer-valued function on its places over $\overline{\mathbb{Q}}$, with $D(W) = \operatorname{ord}_W(f)$ for every place $W$, where $\operatorname{ord}_W$ is minus the logarithm of the adic valuation attached to $W$. Then for every place $c$ which is of infinity side for $P$, meaning that $c$ is cuspidal for $P$ and there is $\tau \in A$ with $\mathrm{red}(\tau) = 1$ and $c$ taking the value $\tau$ on $t_\infty$, the pushforward along $P.\mathrm{reduceFst}$ — restriction of a place along the integral map $\overline{\alpha}$ followed by $P.\mathrm{sp}$ — of the restriction of $D$ to the infinity-side places, evaluated at $P.\mathrm{reduceFst}(c)$, equals the order at $P.\mathrm{reduceFst}(c)$ of the residue $R.\mathrm{residue}_1(f)$. The conclusion is asserted at every infinity-side place $c$, not only at the cusp at infinity.
--
--   This is the cusp law at infinity, in its one-sided form at auxiliary level $N = 1$: the pushforward of the infinity-side part of the divisor of $f$ computes the order of the reduction of $f$ on the characteristic-$q$ model. It is used in the construction of good divisors, of admissible translates of integral functions, and of the component charts and annuli attached to a model prolongation tuple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided_levelOne.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided_levelOne {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        (∀ W, D W = W.ord f) →
        ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
          IsInftySide P c →
          Finsupp.mapDomain P.reduceFst (D.filter (IsInftySide P)) (P.reduceFst c)
            = (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩) := by sorry
