-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_power_four_padding
-- name    : ITPIRPreproc.MatchVec.power_four_padding
-- status  : Open
-- author  : @Jesko
-- created : 2026-11-13T16:46:40.797203+00:00
-- url     : https://prove2.me/theorems/cc795a33-9a04-4021-a420-081c4221c465
-- title:
--   Padding transfer: PIR at power-of-four database lengths implies PIR at every database length
-- statement:
--   Suppose one uniform single-server PIR scheme with streaming client preprocessing satisfies the following for every integer $h\ge3$ and security parameter $\lambda\ge1$, at database length $N=4^h$: perfect privacy, correctness error at most $T2^{-\lambda}$, preprocessing work $K N^{1+\eta(h)}\lambda^c$, online communication $K\lambda N^{\eta(h)}$, offline communication $K\sqrt N$, and preprocessing storage, client storage, and client/server work per retrieval bounded by $K N^{1/2+\eta(h)}\lambda^c$, for constants $K,c$ and $\eta(h)\to0$.
--
--   Then there is one uniform scheme for every database length $n\ge1$, a function $\varepsilon(n)\to0$, and constants $C,c'$ with perfect privacy, correctness error at most $T2^{-\lambda}$, and bounds
--   $$\text{preprocessing work}\le C n^{1+\varepsilon(n)}\lambda^{c'},\quad
--   \text{online communication}\le C\lambda n^{\varepsilon(n)},\quad
--   \text{offline communication}\le C\sqrt n,$$
--   while preprocessing storage, client storage, and client/server work per retrieval are at most
--   $$C n^{1/2+\varepsilon(n)}\lambda^{c'}.$$
--   All bounds are worst-case and include the temporary storage specified by the PIR model. The scheme never receives the number of retrievals as input.
--
--   This is the padding step used after the power-of-two matrix construction in the proof of Theorem 6.1. It isolates the passage from matrix-sized databases to arbitrary lengths, including implementation overhead and adaptive privacy/correctness.
--
--   **Formalization Note** The hypothesis packages the scheme and all its constants existentially. The conclusion is the resource specification of Theorem 6.1. This is a generalization of the paper's padding step to any uniform scheme satisfying the displayed power-of-four bounds; it does not assume the matching-vector construction or compiler.
-- source:
--   Dujmovic, Lai, Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/572.pdf, §5.2 printed p.16 (padded matrix layout), proof of Theorem 5.1 printed p.20 (padding changes bounds by a constant factor), proof of Theorem 6.1 printed p.24.

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_ITPIRPreproc_MatchVec_Model
open scoped ENNReal
open Filter Topology

namespace ITPIRPreproc.MatchVec

theorem power_four_padding
    (hSquare :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
        ∃ (K : ℝ) (c : ℕ), ∀ h lam : ℕ, 3 ≤ h → 1 ≤ lam →
          PerfectlyPrivate S (4^h) lam ∧
          Correct S (4^h) lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞)^lam) ∧
          MeetsBudget S (4^h) lam
            { preWork := K * ((4^h : ℕ) : ℝ)^(1+η h) * (lam:ℝ)^c
              preSpace := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              online := K * lam * ((4^h : ℕ) : ℝ)^(η h)
              offline := K * Real.sqrt (4^h : ℕ)
              clientWork := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              clientSpace := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              serverWork := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c }) :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∃ (C : ℝ) (c : ℕ), ∀ n lam : ℕ, 1 ≤ n → 1 ≤ lam →
          PerfectlyPrivate S n lam ∧
          Correct S n lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ lam) ∧
          MeetsBudget S n lam
            { preWork := C * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c
              preSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              online := C * lam * (n : ℝ) ^ (ε n)
              offline := C * Real.sqrt n
              clientWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              clientSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              serverWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c } := by sorry

end ITPIRPreproc.MatchVec
