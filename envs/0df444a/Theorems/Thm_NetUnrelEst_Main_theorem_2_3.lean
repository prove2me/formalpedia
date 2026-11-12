-- Prove2me | Theorems.Thm_NetUnrelEst_Main_theorem_2_3
-- name    : NetUnrelEst.Main.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:39.072092+00:00
-- url     : https://prove2.me/theorems/1f0f684d-f1df-43fb-b558-d06f460bb6ad
-- title:
--   Theorem 2.3 — x ≤ C_β u^{3/2} for polynomially small u
-- statement:
--   For every $\beta>0$ there are constants $C_\beta$ and $n_\beta$ such that every connected multigraph with $n\ge n_\beta$ vertices and independent failure probabilities $p_e\in[0,1]$ with $u\le n^{-\beta}$ satisfies
--   $$x=\sum_{C\ne C'}a_{C\cup C'}\le C_\beta\,u^{3/2}.$$
--
--   This is the paper's cut-intersection theorem: in a very reliable graph, two distinct cuts rarely fail together, so disconnection happens essentially at one cut. The exponent $3/2$ is sharp on a cycle. With (7) it gives $z=u+O(u^{3/2})$, and the recursive estimator's variance bound rests on it.
--
--   **Formalization Note.** $C_\beta$ and $n_\beta$ are quantified before the graph and the probabilities. The sum is over ordered pairs of distinct cuts, and $u^{3/2}$ is a real power.
--
--   Differences from the source:
--   - generalization: the graph G of the paper with p_e ∈ [0,1] (proved for 0 < p_e < 1 and extended by approximation, keeping the graph fixed) → any connected multigraph on Fin n (self-loops and parallel edges allowed) with p ∈ [0,1]^m; reason: loops cross no cut and parallel edges combine into one edge with the product failure probability, leaving u and x unchanged; the paper's graph is one instance
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 10, Theorem 2.3

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Theorem 2.3.** For every `β > 0` there are constants `C_β, n_β` such that every connected
multigraph with `n ≥ n_β` vertices and failure probabilities `p ∈ [0,1]^m` with `u ≤ n^{−β}`
satisfies `x ≤ C_β u^{3/2}`. Sun 2027, p. 10, Theorem 2.3. -/
theorem theorem_2_3 (β : ℝ) (hβ : 0 < β) :
    ∃ Cβ : ℝ, ∃ nβ : ℕ, ∀ {n m : ℕ} (ends : Ends n m), IsConnectedGraph ends →
      ∀ p : Fin m → ℝ, (∀ e, 0 ≤ p e ∧ p e ≤ 1) → nβ ≤ n → unrel ends p ≤ (n : ℝ) ^ (-β) →
        xSum ends p ≤ Cβ * unrel ends p ^ ((3 : ℝ) / 2) := by sorry

end NetUnrelEst.Main
