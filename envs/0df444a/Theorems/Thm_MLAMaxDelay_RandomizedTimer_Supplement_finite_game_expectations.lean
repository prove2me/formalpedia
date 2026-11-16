-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_finite_game_expectations
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.finite_game_expectations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:57:49.362004+00:00
-- url     : https://prove2.me/theorems/bd9fad37-b878-4902-8288-0185afb073cb
-- title:
--   Lemma A.3 — online and offline expectations of the (m, K) game
-- statement:
--   Let $T$ be a weighted rooted tree, $v$ a vertex of root-path weight $c>0$, and $m,K\ge2$ integers. Let $I$ be drawn from the $(m,K)$ distribution of equation (31) at $v$, with $q_m=1-(1-1/m)^m$ and
--
--   $$A_{m,K}=\sum_{i=0}^{K-1}q_m^i,\qquad B_{m,K}=q_m\sum_{i=0}^{K-2}q_m^i+q_m^{K-1}.$$
--
--   Then the distribution has total mass $1$; every deterministic online algorithm satisfies $\mathbb E_I[\mathrm{ALG}(I)]\ge c\,A_{m,K}$; and $\mathbb E_I[\mathrm{OPT}(I)]=c\,B_{m,K}$.
--
--   The ratio $A_{m,K}/B_{m,K}$ tends to $e/(e-1)$, which yields the randomized lower bound of Theorem A.4.
--
--   Differences from the source:
--   - encoding: finite rooted tree with nonnegative edge weights and at least one positive edge (Section 2 standing assumption) → the published WeightedTree (parent map, nonnegative non-root weights, a positive edge); reason: the base mission's moderated model; every source tree is represented
--   - encoding: finite labelled request occurrences → a Finset of natural-number labels with arrival and location maps (published Input); reason: every finite labelled input admits an injective relabelling; simultaneous arrivals and repeated locations are kept
--   - encoding: costs in ℝ with +∞ for an infeasible schedule; OPT the minimum over feasible offline schedules → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules (published cost and optimum); reason: the same values; attainment is part of the base milestones
--   - encoding: an input drawn from the (m, K) distribution and E_I → explicit finite weights over gap-index sequences of length ≤ K−1 and weighted sums in ℝ≥0∞; reason: the distribution has finite support; ALG may be +∞
--   - encoding: the resulting distribution (p. 19, with Σ p_j = 1 − s_m) → total mass 1 is a conclusion; reason: the source asserts it is a probability distribution; stating it excludes a vacuous weighting
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 20, Lemma A.3; p. 19, equations (31)–(34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_LowerBound

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Lemma A.3, p. 20, both conclusions, for the `(m, K)` distribution (31) at a node `v` of path
cost `c > 0`: every deterministic online algorithm has `E_I[ALG(I)] ≥ c·A_{m,K}` and
`E_I[OPT(I)] = c·B_{m,K}`. The distribution's total mass is `1`. -/
theorem finite_game_expectations {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (v : V) (hc : 0 < pathCost T v)
    (m K : ℕ) (hm : 2 ≤ m) (hK : 2 ≤ K) :
    gameMass m K = 1 ∧
    (∀ A : Input V → Schedule V, Causal A →
      ENNReal.ofReal (pathCost T v * gameA m K) ≤
        gameExpect T v m K (fun I => cost T I (A I))) ∧
    gameExpect T v m K (fun I => optimum T I) =
      ENNReal.ofReal (pathCost T v * gameB m K) := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
