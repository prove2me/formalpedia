-- Prove2me | Theorems.Thm_HScattered_Bound_proposition_2_1
-- name    : HScattered.Bound.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:25.291658+00:00
-- url     : https://prove2.me/theorems/7577a8ea-e979-4de7-91df-8ec7efbce214
-- title:
--   Proposition 2.1 — an h-scattered subspace is i-scattered for every 0 < i < h
-- statement:
--   Let $V$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$ and let $U$ be an $h$-scattered $\mathbb F_q$-subspace of $V$ with $h > 1$. Then for every integer $i$ with $0 < i < h$, the subspace $U$ is also $i$-scattered:
--
--   $$
--   \dim_{\mathbb F_q}(S \cap U) \le i \qquad\text{for every } i\text{-dimensional } \mathbb F_{q^n}\text{-subspace } S \text{ of } V .
--   $$
--
--   In particular every $h$-scattered subspace is $1$-scattered, so $h$-scattered subspaces form a special class of scattered subspaces. The proposition is used twice in the proof of the main bound (Theorem 2.3) to pass from $h$-scattered to $t$-scattered subspaces for smaller $t$.
--
--   **Formalization Note** $\mathbb F_q$, $\mathbb F_{q^n}$ are finite fields `F`, `K` and $V$ is finite-dimensional over `K`. The range $0 < i$ is required because "$i$-scattered" is only defined for $i > 0$ (Definition 1.1); $i < h < r$ then gives the rest of the range.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 3, Proposition 2.1

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered

namespace HScattered.Bound

/-- Proposition 2.1 (arXiv:1906.10590v2, p. 3). For `h > 1`, an `h`-scattered `𝔽_q`-subspace
of `V(r, qⁿ)` is also `i`-scattered for every `0 < i < h`; in particular it is 1-scattered. -/
theorem proposition_2_1 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h i : ℕ) (U : Submodule F V) (hh : 1 < h) (hU : IsHScattered F K h U)
    (hi0 : 0 < i) (hih : i < h) :
    IsHScattered F K i U := by sorry

end HScattered.Bound
