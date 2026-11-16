-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_theorem_1_2
-- name    : OddPermSum.Evaluation.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:16.55422+00:00
-- url     : https://prove2.me/theorems/e13b5f1c-6e70-40de-ada9-1cc894e799e1
-- title:
--   Theorem 1.2 (companion theorem; not used in the proof of the goal) — Shortest even length and full arc union
-- statement:
--   Fix a uniformly bilinear admissible exponent $2<\omega\le3$. There exist one randomized finite bit-RAM program and constants $C>0$, $k\in\mathbb N$, all chosen before the input graph. For every loopless simple digraph $D$ on $n$ vertices that has an even directed cycle, let $\ell$ be the shortest even-cycle length and $E_\ell$ the union of the arcs of all such cycles. With probability at least $1-Cn^{-3}$, the program outputs exactly $(\ell,E_\ell)$ within
--   $$C n^\omega\ell\bigl(\log_2(n+1)+1\bigr)^k$$
--   steps. Every execution halts within $C n^{\omega+1}(\log_2(n+1)+1)^k$ steps. The input is the directed adjacency matrix, and the arc union is explicitly output as membership bits.
--
--   Both correctness and the length-sensitive time bound belong to the same success event. The unconditional horizon is independent of the random tape.
--
--   Differences from the source:
--   - encoding: vertices indexed by [n] and cycles up to rotation → vertices indexed by Fin n and cycles represented by their directed arc sets; reason: zero-based relabeling and rotation quotient preserve every directed cycle, including length two
--   - reading: a fixed admissible matrix multiplication exponent, with a bilinear algorithm used on p. 14 → UniformBilinearExponent with prime-field coefficients and an effective uniform circuit generator; reason: the changing finite fields require one uniform algorithm and the bilinear polynomial identity must lift to the truncated algebra; this is the structured brief’s prescribed reading
--   - encoding: time and probability as on p. 2, including its sentence after Theorem 1.3 → finite bit-RAM program with empty advice, a joint correctness/time event of probability at least 1-C n^(-3), and a bound on every tape; reason: charges control and finite-field construction and makes both source time guarantees explicit
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Theorem 1.2 (proof pp. 15–16)

import Definitions.Def_OddPermSum_Evaluation_Supplement_bilinearMultiplier
import Definitions.Def_OddPermSum_Evaluation_Supplement_graphOutputs

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem theorem_1_2 (ω : ℝ) (hω : UniformBilinearExponent ω) :
    ∃ (p : BitProgram) (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (n : ℕ) (D : Digraph n) (ℓ : ℕ), IsShortest D ℓ → ∃ T : ℕ,
      (T : ℝ) ≤ C * (n : ℝ)^(ω+1) * logFactor n k ∧ graphHalts p D T ∧
      supportSuccess p D ℓ T (C * (n : ℝ)^ω * ℓ * logFactor n k) ≥
        1 - C * (n : ℝ)^(-(3 : ℝ)) := by sorry

end OddPermSum.Evaluation.Supplement
