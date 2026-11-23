-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_corollary_1
-- name    : MLRPCake.EnvyFree.Supplement.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:07:45.524797+00:00
-- url     : https://prove2.me/theorems/f6d0d26e-2df0-4811-9a11-ab1fbcb29bbd
-- title:
--   Corollary 1 — a switching point can be localized to an interval of length at most γ with O(log(1/γ)) Eval queries
-- statement:
--   Let $f_i,f_j$ be value densities of agents $i<j$ of a cake-division instance with MLRP (so $f_i,f_j$ bear MLRP), and let $\gamma\in(0,1)$. Run the binary search over dyadic cells of mesh $2^{-K}$, $K=\lceil\log_2(2/\gamma)\rceil$, using two Eval queries per iteration. It returns an interval $[a,b]$ with
--   $$a\le p_{ij}\le b,\qquad b-a\le\gamma,$$
--   and it makes $2K$ queries, which is at most $c\,(\log_2(1/\gamma)+1)$ for a universal constant $c$, i.e. $O(\log(1/\gamma))$.
--
--   Applied with $\gamma=\eta/(n\lambda)$ to every pair of agents, this computes the switching points to the precision needed by the social-welfare algorithm of Theorem 3.
--
--   Differences from the source:
--   - encoding: two value densities f_i, f_j that bear MLRP → agents i < j of an instance satisfying IsInstance and IsMLRP; reason: any MLRP pair is a two-agent MLRP instance, and pairs i < j of an MLRP instance bear MLRP by transitivity (p. 7); same pairs
--   - reading: we can find an interval of length γ that contains p_ij → the returned interval [a, b] contains p_ij and has b − a ≤ γ; reason: a shorter interval containing p_ij extends to one of length exactly γ; the proof returns two cells of length γ/2
--   - encoding: in O(log(1/γ)) time, by binary search over cells of width γ/2, k ∈ {1,…,2/γ} → the concrete binary search over dyadic cells of mesh 2^{-K}, K = ⌈log₂(2/γ)⌉, with 2K Eval queries bounded by c·(log₂(1/γ)+1), c universal; reason: the source's cells presuppose 2/γ ∈ ℕ; the dyadic mesh is at most γ/2 for every γ ∈ (0,1) and keeps the logarithmic count
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 18, Corollary 1 (proof pp. 18–19)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints

namespace MLRPCake.EnvyFree.Supplement

/-- Corollary 1, p. 18: for agents `i < j` of an MLRP instance (so `f_i, f_j` bear MLRP) and
`γ ∈ (0,1)`, the binary search over cells of mesh `2^{-K}`, `K = ⌈log₂(2/γ)⌉`, using two Eval
queries per iteration, returns an interval of length at most `γ` containing the switching point
`p_{ij}`, and its number of queries is `O(log(1/γ))` (universal constant). -/
theorem corollary_1 : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (i j : Fin n) (γ : ℝ),
    IsInstance f → IsMLRP f → i < j → 0 < γ → γ < 1 →
    locLeft f i j γ ≤ switchPt (f i) (f j) ∧ switchPt (f i) (f j) ≤ locRight f i j γ ∧
      locRight f i j γ - locLeft f i j γ ≤ γ ∧
      (locQueries γ : ℝ) ≤ c * (Real.logb 2 (1 / γ) + 1) := by sorry

end MLRPCake.EnvyFree.Supplement
