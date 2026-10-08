-- Prove2me | Theorems.Thm_KallenbergLP_Contracting_convexHull_KD_eq_KS_eq_KM_eq_K_eq_P
-- name    : KallenbergLP.Contracting.convexHull_KD_eq_KS_eq_KM_eq_K_eq_P
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:34:58.410036+00:00
-- url     : https://prove2.me/theorems/47b8e237-7eca-477a-a36f-0b00d717f646
-- title:
--   Theorem 3.4.8 — all policy frequency sets equal the LP polytope
-- statement:
--   Let $\beta$ be any initial probability distribution in a finite contracting Markov decision model; some coordinates of $\beta$ may be zero. Let $K(D)$, $K(S)$, $K(M)$, and $K$ be the state-action frequency sets of pure stationary, stationary, Markov, and general history-dependent randomized policies, and let $P$ be the nonnegative solution set of the flow equalities. Then
--
--   $$\overline{K(D)}=K(S)=K(M)=K=P,$$
--
--   where the bar denotes **closed convex hull**. As $K(D)$ is finite, the Lean statement uses its convex hull, which is already closed.
--
--   The result says that allowing randomized and history-dependent choices creates no new frequency vectors beyond mixtures of pure stationary policies. The zero entries permitted in $\beta$ make the stationary-policy map non-injective, so the conclusion is about sets of frequencies rather than a bijection.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 73, Theorem 3.4.8; p. 9, Definition 1.2.1(i) (overbar convention)

import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.8, p. 73. The overbar in the book
denotes closed convex hull; `KD` is finite, so its convex hull is closed. -/
theorem convexHull_KD_eq_KS_eq_KM_eq_K_eq_P
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M)
    (β : E → ℝ) (hβ : IsInitialDistribution β) :
    convexHull ℝ (M.KD β) = M.KS β ∧
    M.KS β = M.KM β ∧
    M.KM β = M.K β ∧
    M.K β = M.feasibleFrequency β := by sorry

end KallenbergLP.Contracting
