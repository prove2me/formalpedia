-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_theorem_1_3
-- name    : OddPermSum.Evaluation.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:45:39.0206+00:00
-- url     : https://prove2.me/theorems/0f1a9507-1f12-45fc-8f18-4c2718e551f2
-- title:
--   Theorem 1.3 (companion theorem; not used in the proof of the goal) — Explicit shortest even-cycle extraction
-- statement:
--   Fix a uniformly bilinear admissible exponent $2<\omega\le3$. There exist one randomized finite bit-RAM program and constants $C>0$, $k\in\mathbb N$, all preceding the graph input. Whenever $D$ is a loopless simple digraph on $n$ vertices with shortest even-cycle length $\ell$, the program outputs an explicit verified simple directed cycle of length $\ell$ within
--   $$C\bigl(n^\omega\ell+n^2\ell^2\bigr)\bigl(\log_2(n+1)+1\bigr)^k$$
--   steps, with probability at least $1-Cn^{-3}$. Every execution halts within $Cn^4(\log_2(n+1)+1)^k$ steps.
--
--   The output encodes the complete closed vertex sequence. Correctness and the length-sensitive bound hold jointly, and the general bound applies to every random tape.
--
--   Differences from the source:
--   - encoding: vertices indexed by [n] and cycles up to rotation → vertices indexed by Fin n and cycles represented by their directed arc sets; reason: zero-based relabeling and rotation quotient preserve every directed cycle, including length two
--   - reading: a fixed admissible matrix multiplication exponent, with a bilinear algorithm used on p. 14 → UniformBilinearExponent with prime-field coefficients and an effective uniform circuit generator; reason: the changing finite fields require one uniform algorithm and the bilinear polynomial identity must lift to the truncated algebra; this is the structured brief’s prescribed reading
--   - encoding: time and probability as on p. 2, including its sentence after Theorem 1.3 → finite bit-RAM program with empty advice, a joint correctness/time event of probability at least 1-C n^(-3), and a bound on every tape; reason: charges control and finite-field construction and makes both source time guarantees explicit
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Theorem 1.3 (proof p. 22)

import Definitions.Def_OddPermSum_Evaluation_Supplement_bilinearMultiplier
import Definitions.Def_OddPermSum_Evaluation_Supplement_graphOutputs

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem theorem_1_3 (ω : ℝ) (hω : UniformBilinearExponent ω) :
    ∃ (p : BitProgram) (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (n : ℕ) (D : Digraph n) (ℓ : ℕ), IsShortest D ℓ → ∃ T : ℕ,
      (T : ℝ) ≤ C * (n : ℝ)^4 * logFactor n k ∧ graphHalts p D T ∧
      cycleSuccess p D ℓ T (C * ((n : ℝ)^ω * ℓ + (n : ℝ)^2 * (ℓ : ℝ)^2) * logFactor n k) ≥
        1 - C * (n : ℝ)^(-(3 : ℝ)) := by sorry

end OddPermSum.Evaluation.Supplement
