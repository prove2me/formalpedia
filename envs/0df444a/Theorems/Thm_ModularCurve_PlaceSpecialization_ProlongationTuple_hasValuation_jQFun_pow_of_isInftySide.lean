-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_pow_of_isInftySide
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.hasValuation_jQFun_pow_of_isInftySide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/08e8c948-60ec-5ab0-8516-0323d6345ce7
-- title:
--   Valuation of the q-transform of j on the infinity side
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$ (the ambient algebraic closure of $\mathbb{Q}$), $N \geq 1$, and $k$ a field of characteristic $q$ equipped with a ring homomorphism $\mathrm{red} : A \to k$; let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), `hKr` the Kronecker congruence asserting that $\Phi$ reduced modulo $q$ equals $(C X^q - X)(C X - X^q)$, and `hα`, `hβ` the integrality of the two Hecke maps at level $(N, q)$ over $\overline{\mathbb{Q}}$. Given a specialization datum $P$ of type `PlaceSpecialization A q N data hKr k red hα hβ` and a place $W$ of the function field `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$, assume $W$ lies on the infinity side of $P$, i.e. $W$ is cuspidal for $P$ and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that the chart $t_\infty = j_q/j^{\,q}$ takes at $W$ the value $\tau$ (the element lies in the valuation ring of $W$ and its residue is the image of $\tau$). Assume further that, for some $\gamma$ in the value group of $A$, the function `jFun N q` (the $q$-series $j$ viewed in that function field) has $A$-valuation $\gamma$ at $W$, meaning there exists $J \in \overline{\mathbb{Q}}$ which is the value of `jFun N q` at $W$ with $A$-valuation $\gamma$. Then `jQFun N q`, the $q$-transform $j(\mathfrak{q}^q)$ in the same field, has $A$-valuation $\gamma^q$ at $W$: some element of $\overline{\mathbb{Q}}$ is its value at $W$ and has $A$-valuation $\gamma^q$.
--
--   On the infinity branch of the cuspidal region of $X_0(Nq)$ the two degeneracy maps behave asymmetrically: the $q$-transform of $j$ is deeper than $j$ by exactly a factor $q$ in the valuation, reflecting that the Tate curve $E_{t^q}$ is the quotient of $E_t$ by its canonical subgroup. The statement feeds the identification of the second reduction with the Frobenius twist of the first at infinity-side places where `jQFun` has non-negative order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_pow_of_isInftySide.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.hasValuation_jQFun_pow_of_isInftySide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : IsInftySide P W)
    {γ : A.ValueGroup} (hj : W.HasValuation A (jFun N q) γ) :
    W.HasValuation A (jQFun N q) (γ ^ q) := by sorry
