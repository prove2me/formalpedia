-- Prove2me | Theorems.Thm_LocalDOvS_SUS_lemma_EC_6
-- name    : LocalDOvS.SUS.lemma_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:50.73326+00:00
-- url     : https://prove2.me/theorems/7b85ed31-b4a9-49f2-8d78-39c7245eb3d3
-- title:
--   Lemma EC.6, p.ec11 (corrected: $\log(4N^2/\delta)$ and $+N$, surely)
-- statement:
--   Let $N\ge2$, $\sigma>0$, $\epsilon>0$ and $\delta\in(0,1]$. For every rule choosing the Type-I pair and breaking the final tie and for **every** tape $\omega$, the corrected shrinking uniform sampling algorithm stops, and its number of simulations satisfies
--
--   $$
--   \tau(\omega)\le\frac{25600\,\sigma^2}{\epsilon^2}\log\frac{4N^2}{\delta}+N .
--   $$
--
--   In particular $\mathbb E[\tau]\le 25600\,\sigma^2\epsilon^{-2}\log(4N^2/\delta)+N$ on every model, which is the cost half of Theorem 2.
--
--   Differences from the source:
--   - correction: 25600σ²/ϵ² · log[4N/δ] → 25600σ²/ε² · log(4N²/δ) + N; reason: log(4N²/δ) comes from T_max = N² of the corrected algorithm; the + N pays for rounding each sample size up to an integer, which the printed bound ignores; the printed bound is false for the algorithm: as ε → ∞ it tends to 0 while every run makes at least N ≥ 2 simulations (every point is sampled at least once)
--   - generalization: expected simulation cost → every tape (surely); reason: implies the expectation bound; p.10 states that the upper bounds also hold almost surely
--   - generalization: Algorithm 2 (some pair in line 11) → every pick and tie rule; reason: contains every choice
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Lemma EC.6, p.ec11

import Mathlib
import Definitions.Def_LocalDOvS_SUS_sus
import Definitions.Def_LocalDOvS_SUS_stopTime

open scoped NNReal

namespace LocalDOvS.SUS

/-- **Lemma EC.6, p.ec11** (Zhang–Zheng–Lavaei, arXiv:2012.02427v2), for the corrected
algorithm. For `N ≥ 2`, `σ > 0`, `ε > 0`, `δ ∈ (0, 1]`, every pick and tie rule and **every**
tape `ω`, the corrected shrinking uniform sampling algorithm stops, after at most
`25600 σ²/ε² · log(4N²/δ) + N` simulations.

**Formalization Note.** The corrected `T_max = N²` gives `log(4N²/δ)` for the printed
`log(4N/δ)`. The `+ N` pays for rounding the per-point sample sizes up to integers, which the
printed lemma ignores (the paper's Theorem 2 carries the `+ N`). The bound holds surely, which
implies the expectation bound of the lemma (and p.10: "the upper bounds derived in this paper
also hold almost surely"). -/
theorem lemma_EC_6 (N : ℕ) (hN : 2 ≤ N) (σ : ℝ≥0) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool)
    (ω : ℕ × ℕ → ℝ) :
    stopTime (sus N σ ε δ pick tie) ω ≠ ⊤ ∧
      ((stopTime (sus N σ ε δ pick tie) ω).toNat : ℝ) ≤
        25600 * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (4 * (N : ℝ) ^ 2 / δ) + N := by sorry

end LocalDOvS.SUS
