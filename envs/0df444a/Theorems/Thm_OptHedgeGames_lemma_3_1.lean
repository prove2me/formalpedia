-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_3_1
-- name    : OptHedgeGames.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:39.289114+00:00
-- url     : https://prove2.me/theorems/7c69d652-2bbf-4e78-8d65-c167f3b5b82f
-- title:
--   Lemma 3.1 — the variance RVU inequality for Optimistic Hedge
-- statement:
--   A player with $n\ge1$ actions runs Optimistic Hedge with learning rate $\eta$ against an arbitrary sequence $\ell^1,\dots,\ell^T\in[0,1]^n$ of loss vectors, with $\ell^0=0$. For $0<\eta\le1/8$,
--   $$
--   \mathrm{Reg}(T)\le\frac{\log n}{\eta}+\frac{2\eta}{3}D(T)-\frac{\eta}{3}V(T).
--   $$
--   This reduces a regret bound to an inequality between the total variation $D(T)$ and the cumulative variance $V(T)$ along the trajectory.
--
--   Differences from the source:
--   - encoding: a loss sequence ℓ¹, …, ℓᵀ with ℓ⁰ = 0 → ℓ : ℕ → Fin n → ℝ with ℓ 0 = 0 and [0,1] entries in rounds 1, …, T; reason: rounds past T are not read by the statement
--   - encoding: player i with n actions (no bound on n) → 1 ≤ n; reason: no strategy exists at n = 0
--   - encoding: the horizon T, a number of rounds (§2, p.4; Theorem 3.4 says T ≥ 1) → 1 ≤ T; reason: T = 0 is no horizon; the source's horizon is a positive number of rounds
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), §3.1, p.4; Lemma 3.1, (5), p.5

import Mathlib
import Definitions.Def_OptHedgeGames_OptimisticHedge

namespace OptHedgeGames

/-- **Lemma 3.1** (variance RVU; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma 3.1 with the setting of §3.1, pp.4–5, proved p.44). A
player with `n` actions runs Optimistic Hedge against an arbitrary sequence
`ℓ¹, …, ℓᵀ ∈ [0,1]ⁿ` of loss vectors, with `ℓ⁰ = 0`. For `0 < η ≤ 1/8`,
`Reg(T) ≤ log n/η + (2η/3) D(T) − (η/3) V(T)`, which is (5).

**Formalization Note** The sequence is any `ℓ : ℕ → Fin n → ℝ`, not a game trajectory; only its
rounds `0, …, T` matter. `n ≥ 1` (no strategy exists at `n = 0`). `Real.log` is the natural
logarithm. -/
theorem lemma_3_1 {n : ℕ} (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 8)
    (ℓ : ℕ → Fin n → ℝ) (hℓ0 : ℓ 0 = 0) (T : ℕ) (hT : 1 ≤ T)
    (hℓ : ∀ t ∈ Finset.Icc 1 T, ∀ a, ℓ t a ∈ Set.Icc (0 : ℝ) 1) :
    reg (ohIter η ℓ) ℓ T ≤
      Real.log (n : ℝ) / η + 2 * η / 3 * totalVariation (ohIter η ℓ) ℓ T
        - η / 3 * cumVariance (ohIter η ℓ) ℓ T := by sorry

end OptHedgeGames
