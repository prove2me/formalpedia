-- Prove2me | Theorems.Thm_FreeWeaver_Walk_theorem_1_1
-- name    : FreeWeaver.Walk.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:34:01.408491+00:00
-- url     : https://prove2.me/theorems/c236f4ab-b442-438b-a345-79e0088066b0
-- title:
--   Theorem 1.1 — signs with ‖Σσᵢvᵢvᵢ*‖ < 58√ε, found by a deterministic polynomial-time real-arithmetic algorithm
-- statement:
--   Let $v_1,\dots,v_n\in\mathbb C^m$ satisfy $\sum_iv_iv_i^*=I_m$ and $\|v_i\|^2\le\varepsilon$ for all $i$. Then there are signs $\sigma\in\{-1,1\}^n$ with
--   $$\Big\|\sum_{i=1}^n\sigma_iv_iv_i^*\Big\|<58\sqrt\varepsilon$$
--   (operator norm), and a deterministic algorithm returns such signs in time polynomial in $m$ and $n$ in the real-arithmetic model, with constants independent of the entries. Formally: one program $P$ of the published real RAM (`MatMulTimeLP.RealRAM`) that is `FewInnerTSP.Admissible` (exact $+,-,\times,\div,\sqrt{\cdot}$, comparisons, rational literals, no random draws), and $C,K\in\mathbb N$, all fixed before the input, such that for every $n,m$ and every Parseval family the run on $[n,m,\operatorname{Re}v_1(1),\operatorname{Im}v_1(1),\dots]$ halts at a step $t$ with $t+1\le C(n+m+2)^K$, its $n$ output cells are signs, and they satisfy the bound for every $\varepsilon>0$ with $\|v_i\|^2\le\varepsilon$. Weaver showed that such an $O(\sqrt\varepsilon)$ bound uniform in $m,n$ is equivalent to the Kadison–Singer problem; this is an algorithmic version of Marcus–Spielman–Srivastava.
--
--   Differences from the source:
--   - reading: no lower bound on ε (the statement is false at m = 0, ε = 0, where it reads 0 < 0) → the hypothesis 0 < ε in both clauses; reason: INSIGHTS I1; for m ≥ 1 the other hypotheses give ε ≥ m/n > 0, so no instance with m ≥ 1 is lost
--   - reading: A deterministic algorithm (Algorithm 2 in Section 9) returns such signs → there is a deterministic program that returns such signs; reason: the claim is the existence of a deterministic polynomial-time algorithm; Algorithm 2's own guarantees are Proposition 9.5
--   - encoding: time polynomial in m and n in the real-arithmetic model, constants independent of the entries → one FewInnerTSP-admissible program P of the MatMulTimeLP real RAM and C, K ∈ ℕ chosen before n, m, v; every run halts at t with t + 1 ≤ C·(n + m + 2)^K, every executed instruction counted; reason: the model of p. 2 and p. 66 (arithmetic, comparisons, square roots), with explicit polynomial and constants
--   - encoding: vectors v_i ∈ ℂ^m and the returned signs → the input list [n, m, Re v_1(1), Im v_1(1), …] (weaverInput), the n output cells after the halting step; ε is not an input and the bound holds for every admissible ε > 0; reason: complex data stored by real and imaginary parts (p. 2); Section 9 takes ε = max_i a_i (p. 35)
--   - encoding: the operator norm ‖·‖ of a complex matrix → Mathlib's ℓ² operator norm (opNorm); indices Fin n, Fin m; reason: the same norm
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 2, Theorem 1.1: "Let v1, …, vn ∈ C^m satisfy
Σ_i vi vi* = Im and ∥vi∥² ≤ ε. Then there are signs σ ∈ {−1, 1}^n satisfying
∥Σ_{i=1}^n σi vi vi*∥ < 58√ε. A deterministic algorithm (Algorithm 2 in Section 9) returns such
signs. It runs in time polynomial in m and n in the real-arithmetic model, with constants
independent of the entries of the vectors."
(i) Existence, for every `n`, `m`, every Parseval family and every `ε > 0` bounding all `‖v_i‖²`.
(ii) One admissible (deterministic: rational literals, no draws) program `P` of the published real
RAM and constants `C`, `K`, fixed before the input, such that on the input
`[n, m, Re v_1(1), Im v_1(1), …]` of every Parseval family the run halts at a step `t` with
`t + 1 ≤ C (n + m + 2)^K`, its `n` output cells are signs, and these signs satisfy the bound for
every admissible `ε > 0`. The norm is the operator norm. -/
theorem theorem_1_1 :
    (∀ (n m : ℕ) (v : Fin n → Fin m → ℂ) (ε : ℝ), IsParseval v → (∀ i, sqNorm (v i) ≤ ε) →
      0 < ε → ∃ σ : Fin n → ℝ, IsSigns σ ∧ opNorm (signedSum v σ) < 58 * Real.sqrt ε) ∧
    ∃ (P : MatMulTimeLP.Program) (C K : ℕ), FewInnerTSP.Admissible P ∧
      ∀ (n m : ℕ) (v : Fin n → Fin m → ℂ), IsParseval v → ∀ tape : MatMulTimeLP.Tape,
        ∃ t : ℕ, MatMulTimeLP.HaltsAt P (weaverInput n m v) tape t ∧
          t + 1 ≤ C * (n + m + 2) ^ K ∧
          IsSigns (MatMulTimeLP.outputAt P (weaverInput n m v) tape t n) ∧
          ∀ ε : ℝ, 0 < ε → (∀ i, sqNorm (v i) ≤ ε) →
            opNorm (signedSum v (MatMulTimeLP.outputAt P (weaverInput n m v) tape t n)) <
              58 * Real.sqrt ε := by sorry

end FreeWeaver.Walk
