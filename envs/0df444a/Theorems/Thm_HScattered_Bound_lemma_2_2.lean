-- Prove2me | Theorems.Thm_HScattered_Bound_lemma_2_2
-- name    : HScattered.Bound.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:22.508672+00:00
-- url     : https://prove2.me/theorems/9976c22c-f06b-49fb-af46-42c60023ceb1
-- title:
--   Lemma 2.2 — (r − 1)-scattered 𝔽_q-subspaces of V(r, qⁿ) of every dimension i with r ≤ i ≤ n
-- statement:
--   Let $V$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$ with $r \ge 2$. For every integer $i$ with
--
--   $$
--   r \le i \le n
--   $$
--
--   there exists an $(r-1)$-scattered $\mathbb F_q$-subspace of $V$ of $\mathbb F_q$-dimension $i$; that is, an $i$-dimensional $\mathbb F_q$-subspace $W$ spanning $V$ over $\mathbb F_{q^n}$ and meeting every hyperplane of $V$ in an $\mathbb F_q$-subspace of dimension at most $r-1$.
--
--   In the proof of Theorem 2.3 the lemma is applied in $\mathbb F_{q^n}^{\,h}$ to obtain an $(h-1)$-scattered subspace of dimension $h+1$, which serves as an auxiliary test space.
--
--   **Formalization Note** $q = |\mathbb F_q|$ (`Fintype.card F`), $n = \dim_{\mathbb F_q}\mathbb F_{q^n}$ (`Module.finrank F K`), $r = \dim_{\mathbb F_{q^n}} V$ (`Module.finrank K V`). The hypothesis $r \ge 2$ is not written in the lemma but is forced by Definition 1.1, which requires $0 < r-1$; the paper applies the lemma with $r = h \ge 2$. The lemma is stated for an abstract $V$ rather than for $\mathbb F_{q^n}^{\,r}$; the two are equivalent after a choice of basis.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 3, Lemma 2.2

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered

namespace HScattered.Bound

/-- Lemma 2.2 (arXiv:1906.10590v2, p. 3). Let `V = V(r, qⁿ)` with `r ≥ 2`. For every integer
`i` with `r ≤ i ≤ n` there is an `(r − 1)`-scattered `𝔽_q`-subspace of `V` of dimension `i`.
Here `q = Fintype.card F`, `n = finrank F K`, `r = finrank K V`. -/
theorem lemma_2_2 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (hr : 2 ≤ Module.finrank K V) (i : ℕ)
    (hri : Module.finrank K V ≤ i) (hin : i ≤ Module.finrank F K) :
    ∃ W : Submodule F V, Module.finrank F W = i ∧
      IsHScattered F K (Module.finrank K V - 1) W := by sorry

end HScattered.Bound
