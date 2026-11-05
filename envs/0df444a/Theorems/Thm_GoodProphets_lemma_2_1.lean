-- Prove2me | Theorems.Thm_GoodProphets_lemma_2_1
-- name    : GoodProphets.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:23:26.429618+00:00
-- url     : https://prove2.me/theorems/420761a9-1660-4802-9479-dc5b233afc2c
-- title:
--   Lemma 2.1 — $\mathbb P[\max_\theta|\bar N_\theta(t)-\bar t p_\theta|>\sqrt{\alpha\bar t\log\bar t}]\le 2k\bar t^{-2\alpha}$
-- statement:
--   Let the $T$ arrivals be i.i.d. with distribution $\vec p$ on $k$ types. Let $0\le t\le T$, write $\bar t=T-t$, and let $\bar N_\theta(t)$ be the number of type-$\theta$ arrivals in periods $[t+1,T]$. Then for every real $\alpha$,
--   $$
--   \mathbb P\Big[\max_\theta\big|\bar N_\theta(t)-\bar t\,p_\theta\big|>\sqrt{\alpha\,\bar t\log\bar t}\Big]\le 2k\,\bar t^{-2\alpha}.
--   $$
--   This combines Hoeffding's inequality with a union bound over the $k$ types. Every probabilistic estimate of the paper (Lemmas 3.2, 3.3 and 3.5) is an instance of it.
--
--   **Formalization Note** $\log$ is the natural logarithm. $\max_\theta a_\theta>c$ is written as "$a_\theta>c$ for some $\theta$". For $\alpha<0$ the square root of a negative number is $0$ in Mathlib, and the claim is then trivial because the right-hand side is at least $2$.
--
--   Differences from the source:
--   - encoding: max_θ{|N̄_θ(t) − t̄p_θ|} > c → ∃ θ, c < |N̄_θ(t) − t̄p_θ|; reason: equivalent for a non-empty type set, which Σ p = 1 forces
--   - encoding: P over the arrivals of periods [t + 1, T] → the product law on the whole sequence Fin T → Fin k; reason: the event depends only on those arrivals; same probability
--   - generalization: the standing Assumption 1 (p_θ ≥ β > 0) → any probability vector p; reason: the lemma does not use it; it specializes to the paper's setting
--   - generalization: α, left unquantified by the lemma → every real α; reason: the paper applies it with α = (T log T)^ε/δ² and α = √t̄/δ²; these are instances, and α ≤ 0 is trivial
--   - encoding: "in period t" → t : ℕ with t ≤ T, t = 0 allowed; reason: the proof of Lemma 3.2 applies the lemma at t = 0
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Lemma 2.1, p.7 (proof p.25, A.1)

import Mathlib
import Definitions.Def_GoodProphets_seqProb

namespace GoodProphets

/-- **Lemma 2.1** (Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.7): "In period `t`, we have
`P[max_θ {|N̄_θ(t) − t̄ p_θ|} > √(α t̄ log(t̄))] ≤ 2k t̄^{−2α}`."

Here the `T` arrivals are i.i.d. from the probability vector `p` on `k` types, `t ≤ T`,
`t̄ = T − t`, `N̄_θ(t)` is the number of type-`θ` arrivals in periods `[t + 1, T]`, and `α` is any
real number.

**Formalization Note** `max_θ a_θ > c` is written `∃ θ, c < a_θ` (the type set is non-empty since
`∑ p = 1`). `log` is the natural logarithm, `Real.sqrt` and `Real.rpow` are Mathlib's; for `α < 0`
Mathlib's square root of a negative number is `0`, and then the bound `2k t̄^{−2α} ≥ 2` holds
trivially for `t̄ ≥ 1`. -/
theorem lemma_2_1 {k : ℕ} (p : Fin k → ℝ) (hp0 : ∀ θ, 0 ≤ p θ) (hp1 : ∑ θ, p θ = 1)
    (T t : ℕ) (ht : t ≤ T) (α : ℝ) :
    seqProb p (fun θs : Fin T → Fin k => ∃ θ,
        Real.sqrt (α * ((T - t : ℕ) : ℝ) * Real.log ((T - t : ℕ) : ℝ)) <
          |(countAfter θs t θ : ℝ) - ((T - t : ℕ) : ℝ) * p θ|) ≤
      2 * k * ((T - t : ℕ) : ℝ) ^ (-2 * α) := by sorry

end GoodProphets
