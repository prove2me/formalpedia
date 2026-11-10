-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_8
-- name    : KSATSingleFlip.Connect.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:06:46.192783+00:00
-- url     : https://prove2.me/theorems/2299b22c-08de-4a6b-b444-e9d199088ad1
-- title:
--   Lemma 2.8 — lower bound on the number of solutions
-- statement:
--   Let $\varepsilon_0 = 2^{-k}$, $M = 2^n(1-\varepsilon_0)^m$, $\Gamma = \alpha k^3\varepsilon_0^2$ with $\alpha = m/n$, $L_Z = 40ne^{\Gamma n}$ and $\mathcal Z = \{Z_\Phi\ge M/L_Z\}$. If $\alpha\le 2^k(\ln2 - 1/\ln k) + o_n(1)$ then, for sufficiently large $k$ and $n$,
--   $$\Pr_{\Phi\sim\Phi(k,n,m)}(\mathcal Z)\ \ge\ 1 - \frac1{2n},\qquad \frac{M}{L_Z}\ \ge\ \exp\!\Big(\frac{n}{2\ln k}\Big).$$
--   In Lean: there is $k_0$ such that for every $k\ge k_0$ and every real sequence $\varepsilon_n\to0$ there is $n_0$ with both bounds for all $n\ge n_0$ and all $m$ with $m/n\le 2^k(\ln 2 - 1/\ln k) + \varepsilon_n$.
--
--   Differences from the source:
--   - reading: α ≤ 2^k(ln 2 − 1/ln k) + o_n(1) → ∀ sequence ε_n → 0, ∃ n₀, ∀ n ≥ n₀, ∀ m with m/n ≤ 2^k(ln 2 − 1/ln k) + ε_n; reason: o_n(1) stands for an arbitrary vanishing sequence; quantifying over all of them is the strongest reading (n₀ may depend on the sequence)
--   - encoding: Pr_Φ over Φ(k,n,m) → formulaProb n k m: uniform probability on the published Formula n k m; reason: Φ(k,n,m) is exactly the uniform law on indexed m-tuples of proper k-clauses
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 2.8, printed p. 13 (PDF 15)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model

open scoped Classical BigOperators
open OAI.FixedClauseThreshold Filter Topology

namespace KSATSingleFlip.Connect

/-- Lemma 2.8 (lower bound on the number of solutions; Wang, Yin, Yu, Zhang 2026, printed p. 13).
The hypothesis `α ≤ 2^k (ln 2 − 1/ln k) + o_n(1)` is read as: for every sequence `ε_n → 0` and all
sufficiently large `n`, every `m` with `m/n ≤ 2^k (ln 2 − 1/ln k) + ε_n`. -/
theorem lemma_2_8 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℕ,
        (m : ℝ) / n ≤ (2 : ℝ) ^ k * (Real.log 2 - 1 / Real.log k) + ε n →
          1 - 1 / (2 * (n : ℝ)) ≤ formulaProb n k m (fun F => ZEvent F) ∧
          Real.exp ((n : ℝ) / (2 * Real.log k)) ≤ Mexp n k m / LZ n k m := by sorry

end KSATSingleFlip.Connect
