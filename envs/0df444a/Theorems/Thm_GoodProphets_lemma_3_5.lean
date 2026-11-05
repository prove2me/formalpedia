-- Prove2me | Theorems.Thm_GoodProphets_lemma_3_5
-- name    : GoodProphets.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:08.742392+00:00
-- url     : https://prove2.me/theorems/4bc7283d-8ec4-4ff8-a324-f566d4793007
-- title:
--   Lemma 3.5 — for $t>T/2$, w.p. $\ge1-4k\bar t^{-2\sqrt{\bar t}/\delta^2}$: $\mathrm{OPT}^t_{\theta j}\ge\lfloor\mathrm{TDLP}_{\theta j}(t)-2\bar t^{3/4}\sqrt{\log\bar t}\rfloor$
-- statement:
--   Let $\sigma$ be a tie-breaking rule satisfying Assumption 2 with a constant $\delta>0$. Let the $T$ arrivals be i.i.d. with distribution $\vec p$, with final counts $\vec N$ and counts $\vec N(t)$ in periods $[1,t]$. Consider a period $t$ with $T/2<t\le T$ and write $\bar t=T-t$. With probability at least
--   $$
--   1-4k\,\bar t^{-\left(\frac{2\sqrt{\bar t}}{\delta^2}\right)}
--   $$
--   the following holds. Let $\vec y=\vec x^{\mathrm{ALG}}(t-1)\ge0$ be any record of actions already taken in periods $[1,t-1]$, so that $\sum_jy_{\theta j}=N_\theta(t-1)$ for every $\theta$. Let $\mathrm{OPT}^t=\sigma(\vec N,\vec y)$ be the hindsight-optimal solution of $\min_{\vec x\ge\vec y}f_{\vec N}(\vec x)$ and $\mathrm{TDLP}(t)=\sigma(\tfrac Tt\vec N(t),\vec y)$ that of $\min_{\vec x\ge\vec y}f_{\frac Tt\vec N(t)}(\vec x)$. Then for all $\theta,j$
--   $$
--   \mathrm{OPT}^t_{\theta j}\ \ge\ \Big\lfloor\mathrm{TDLP}_{\theta j}(t)-2\,\bar t^{\frac34}\sqrt{\log\bar t}\Big\rfloor .
--   $$
--   After the heads-up, $\mathrm{TDLP}(t)$ can be computed from the observed arrivals and the known horizon. The lemma turns it into lower confidence bounds, or **budgets**, on how often the hindsight optimum uses each action in the remaining periods. These budgets drive the second phase of Algorithm 1.
--
--   **Formalization Note** $\lfloor\cdot\rfloor$ is the integer floor, $\log$ is natural and $\bar t^{3/4}$ is `Real.rpow`.
--
--   Differences from the source:
--   - generalization: the actions x^ALG(t − 1) already taken by the algorithm → every y ≥ 0 with Σⱼ y_θj = N_θ(t − 1), inside the event; reason: the algorithm's record is one such y; the event holds simultaneously for all of them
--   - encoding: δ, the constant of Assumption 2, in the exponent −2√t̄/δ² → 0 < δ and Selection I σ δ; reason: the bound divides by δ²; δ ≤ 0 is excluded as undefined
--   - generalization: the standing assumptions of §2 (Assumption 1 p_θ ≥ β > 0; f_N real-valued) → any probability vector p; no boundedness hypothesis; reason: the statement does not need them; it specializes to the paper's setting
--   - reading: Assumption 2: a tie-breaking rule "that maintains λ-Lipschitz continuity in the right-hand side"; "the optimal solution" of each program is the selected one (p.8) → σ(N, y) with Selection I σ δ: |σ(N, y) − σ(N′, y)|_∞ ≤ δ|N − N′|_∞ for Σ N = Σ N′; reason: the proof uses the constant δ for the selected solutions; a λ-Lipschitz rule satisfies this with max(λ, δ)
--   - generalization: Assumption 2 "for any N, y" → Selection I σ δ: only for y ≥ 0, N, N′ ≥ 0 with non-empty feasible sets; reason: a weaker hypothesis; the proof applies it to N and (T/t)N(t), whose feasible sets contain points above y
--   - encoding: a period t > T/2 → T/2 < t ≤ T; reason: periods of the horizon are at most T
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Lemma 3.5, p.13; OPTᵗ p.10, TDLP(t) p.13 (proof p.27, A.2)

import Mathlib
import Definitions.Def_GoodProphets_Selection
import Definitions.Def_GoodProphets_seqProb

namespace GoodProphets

/-- **Lemma 3.5** (Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.13): "Consider a period
`t > T/2` with actions `x^ALG_θj(t − 1)` already taken in periods `[1, t − 1]`; with probability at
least `1 − 4k t̄^{−(2√t̄/δ²)}` we have `∀θ, j : OPT^t_θj ≥ ⌊TDLP_θj(t) − 2 t̄^{3/4} √(log t̄)⌋`."

Here `t̄ = T − t`, the `T` arrivals are i.i.d. from `p`, `OPTᵗ = σ(N, y)` is the selected solution
of `min_x f_N(x)` s.t. `x ≥ y` (p.10) and `TDLP(t) = σ((T/t) N(t), y)` that of
`min_x f_{(T/t)N(t)}(x)` s.t. `x ≥ y` (p.13), where `y = x^ALG(t − 1)`.

**Formalization Note** The event is required uniformly over every `y ≥ 0` with
`∑ⱼ y_θj = N_θ(t − 1)` for all `θ` (every possible record `x^ALG(t − 1)` of actions taken on the
first `t − 1` arrivals), so it holds whatever the actions were. `⌊·⌋` is `Int.floor` cast to `ℝ`,
`log` is natural, `t̄^{3/4}` is `Real.rpow`. -/
theorem lemma_3_5 {k ℓ r m : ℕ} (I : Instance k ℓ r m)
    (σ : (Fin k → ℝ) → (Fin k → Fin ℓ → ℝ) → (Fin k → Fin ℓ → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hsel : Selection I σ δ) (p : Fin k → ℝ) (hp0 : ∀ θ, 0 ≤ p θ) (hp1 : ∑ θ, p θ = 1)
    (T t : ℕ) (htT : t ≤ T) (ht : (T : ℝ) / 2 < t) :
    1 - 4 * k * ((T - t : ℕ) : ℝ) ^ (-(2 * Real.sqrt ((T - t : ℕ) : ℝ) / δ ^ 2)) ≤
      seqProb p (fun θs : Fin T → Fin k => ∀ y : Fin k → Fin ℓ → ℝ, (∀ θ j, 0 ≤ y θ j) →
        (∀ θ, ∑ j, y θ j = (countBefore θs (t - 1) θ : ℝ)) →
        ∀ θ j,
          ((⌊σ (fun θ' => (T : ℝ) / t * (countBefore θs t θ' : ℝ)) y θ j -
              2 * ((T - t : ℕ) : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt (Real.log ((T - t : ℕ) : ℝ))⌋ : ℤ) :
            ℝ) ≤ σ (fun θ' => (countAll θs θ' : ℝ)) y θ j) := by sorry

end GoodProphets
