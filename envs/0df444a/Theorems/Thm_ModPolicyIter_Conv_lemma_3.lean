-- Prove2me | Theorems.Thm_ModPolicyIter_Conv_lemma_3
-- name    : ModPolicyIter.Conv.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:14:08.675368+00:00
-- url     : https://prove2.me/theorems/9debc3e9-43d5-45ab-8fc8-aba42387c72b
-- title:
--   Lemma 3, p. 1130 — U^k u ≥ (I + A^k B)v for u ≥ v; (I + A^k B)u ≥ U^0 v if also Bu ≥ 0
-- statement:
--   Throughout, $S$ is a set of states with a $\sigma$-algebra; each policy $P\in\mathcal P$ is a Markov transition kernel on $S$ with a measurable one-period reward $c_P$, $\sup_P\sup_s|c_P(s)|\le M$; $0\le\lambda<1$; $V$ is the space of bounded measurable functions with $\|v\|=\sup_s|v(s)|$; and the maximum in $Bv=\max_P\{c_P+(\lambda P-I)v\}$ is attained for every $v\in V$, a maximizer being written $P_v$.
--
--   Write $(I+A^kB)x=x+A^k_{P_x}Bx$, with $A^k_P=\sum_{i=0}^k(\lambda P)^i$ and $P_x$ a maximizer at $x$. Let $k\ge 0$ and $u,v\in V$ with $v\le u$ pointwise. Then
--
--   1. for every maximizer $P_v$ at $v$,
--   $$U^ku\ \ge\ v+A^k_{P_v}Bv;$$
--   2. if moreover $Bu\ge 0$, then for every maximizer $P_u$ at $u$,
--   $$u+A^k_{P_u}Bu\ \ge\ U^0v.$$
--
--   So one step of modified policy iteration of order $k$ is sandwiched between one step of value iteration and one step of $U^k$-iteration; this is the comparison behind Theorem 1 and Corollary 1.
-- source:
--   Puterman and Shin, Modified policy iteration algorithms for discounted Markov decision problems, Management Science 24 (1978), DOI 10.1287/mnsc.24.11.1127, p. 1130, Lemma 3

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Setting

open MeasureTheory ProbabilityTheory

namespace ModPolicyIter.Conv

/-- Lemma 3 (Puterman–Shin 1978, p. 1130): for `u ≥ v` in `V`, `U^k u ≥ (I + A^k B)v`; if in
addition `u ∈ V_B`, then `(I + A^k B)u ≥ U^0 v`. Here `(I + A^k B)x = x + A^k_x Bx` with `A^k_x`
the truncated series of a maximizer at `x`. -/
theorem lemma_3 {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)
    (hmax : MaxAttained m) (k : ℕ) :
    ∀ u v : S → ℝ, IsBM u → IsBM v → (∀ s, v s ≤ u s) →
      (∀ i, Attains m v i → ∀ s, v s + Apow m i k (B m v) s ≤ U m k u s) ∧
      ((∀ s, 0 ≤ B m u s) → ∀ i, Attains m u i →
        ∀ s, U m 0 v s ≤ u s + Apow m i k (B m u) s) := by sorry

end ModPolicyIter.Conv
