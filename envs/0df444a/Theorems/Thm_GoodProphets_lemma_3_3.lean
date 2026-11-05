-- Prove2me | Theorems.Thm_GoodProphets_lemma_3_3
-- name    : GoodProphets.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:25:48.381795+00:00
-- url     : https://prove2.me/theorems/6bf59cc8-8f37-4f39-91a8-139cd96de27c
-- title:
--   Lemma 3.3 — bad events are rare, and off them $|\mathrm{DLP}_{\theta j}-\mathrm{EDLP}(t)_{\theta j}|<[t\log t]^{(1+\epsilon)/2}/t$
-- statement:
--   Let $\sigma$ be a tie-breaking rule satisfying Assumption 2 with a constant $\delta>0$, and let $\epsilon>0$. Let the arrivals of periods $1,\dots,t$ be i.i.d. with distribution $\vec p$, and let $N_\theta(t)$ be the number of type-$\theta$ arrivals among them. Write $\mathrm{DLP}=\sigma(\vec p,0)$ for the solution of $\min_{\vec x\ge0}f_{\vec p}(\vec x)$ and $\mathrm{EDLP}(t)=\sigma(\vec N(t)/t,0)$ for the solution of the empirical program $\min_{\vec x}f_{\vec N(t)/t}(\vec x)$. The **bad event** of period $t$ is
--   $$
--   S_t=\Big\{\max_\theta|N_\theta(t)-t\,p_\theta|>\frac{[t\log(t)]^{\frac{1+\epsilon}2}}{\delta}\Big\}.
--   $$
--   For every period $t\ge1$ (at $t=2$ with $\epsilon\le1/2$, as Assumption 3 forces):
--
--   1. $\mathbb P[S_t]<2k\,t^{-2t^\epsilon/\delta^2}$;
--   2. with probability at least $1-2k\,t^{-2t^\epsilon/\delta^2}$, for every action $a_{\theta j}$,
--   $$
--   \big|\mathrm{DLP}_{\theta j}-\mathrm{EDLP}(t)_{\theta j}\big|<\frac{[t\log(t)]^{\frac{1+\epsilon}2}}{t}.
--   $$
--
--   The empirical program can be solved without knowing $\vec p$ or $T$, and with high probability its solution is close to that of the deterministic program. The thresholds of Algorithm 1 are taken from this bound.
--
--   **Formalization Note** The probability is over the first $t$ arrivals. $\max_\theta a_\theta>c$ is written as "$a_\theta>c$ for some $\theta$".
--
--   Differences from the source:
--   - reading: |DLP_θj − EDLP(t)_θj| < [t log(t)]^{(1+ε)/2} → |DLP_θj − EDLP(t)_θj| < [t log(t)]^{(1+ε)/2} / t; reason: the printed bound is ≥ 1 for t ≥ 2 while both solutions have entries in [0, 1], so it says nothing; the proof bounds |N(t)/t − p|_∞ by [t log t]^{(1+ε)/2}/(δt) off S_t, and Algorithm 1's threshold [log t]^{(1+ε)/2}/t^{(1−ε)/2} (p.12) is exactly [t log t]^{(1+ε)/2}/t
--   - reading: every period t, with ε the constant of Assumption 3 → t ≥ 1, with the hypothesis ε ≤ 1/2 at t = 2 only; reason: T − T̂ > T^{1/2+ε} forces ε < 1/2 for T ≥ 2, so no case of the paper is excluded; for large ε the case t = 2 fails: k = 2, ℓ = 1, f ≡ 0, σ(N, y)_θ = N_θ, p = (0.18, 0.82), ε = 2, δ = 1; N(2) = (2, 0) has probability 0.0324, is a bad event (|2 − 0.36| = 1.64 > (2 log 2)^{3/2} ≈ 1.632) and gives |DLP − EDLP(2)| = 0.82 > (2 log 2)^{3/2}/2 ≈ 0.816, while 2k t^{−2t^ε/δ²} = 4·2^{−8} ≈ 0.0156
--   - reading: Assumption 2: a tie-breaking rule "that maintains λ-Lipschitz continuity in the right-hand side"; "the optimal solution" of each program is the selected one (p.8) → σ(N, y) with Selection I σ δ: |σ(N, y) − σ(N′, y)|_∞ ≤ δ|N − N′|_∞ for Σ N = Σ N′; reason: the proof uses the constant δ for the selected solutions; a λ-Lipschitz rule satisfies this with max(λ, δ)
--   - encoding: δ, the constant of Assumption 2, in S_t and in the exponent −2t^ε/δ² → 0 < δ and Selection I σ δ; reason: the event and the bound divide by δ; δ ≤ 0 is excluded as undefined
--   - encoding: P over the arrivals of the whole horizon → the product law on the first t arrivals, Fin t → Fin k; reason: both events depend only on those arrivals; same probability
--   - generalization: the standing assumptions of §2 and Assumption 3 (p_θ ≥ β > 0; f_N real-valued; ε < 1/2) → any probability vector p; no boundedness hypothesis; every ε > 0 at t ≠ 2; reason: the statement does not need them; it specializes to the paper's setting
--   - generalization: Assumption 2 "for any N, y" → Selection I σ δ: only for y ≥ 0, N, N′ ≥ 0 with non-empty feasible sets; reason: a weaker hypothesis; the proof applies it at y = 0 to p and N(t)/t
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Lemma 3.3, p.11; bad event S_t, p.11 (proof p.26, A.2); threshold of Algorithm 1, p.12

import Mathlib
import Definitions.Def_GoodProphets_Selection
import Definitions.Def_GoodProphets_seqProb

namespace GoodProphets

/-- **Lemma 3.3** (Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.11): "The probability
of a bad event can be bounded by `P[S_t] < 2k t^{−2t^ε/δ²}`; as a result, with probability at least
`1 − 2k t^{−2t^ε/δ²}` we have for every action `a_θj` that `|DLP_θj − EDLP(t)_θj| < [t log(t)]^{(1+ε)/2}`",
with the bad event `S_t = {max_θ |N_θ(t) − t p_θ| > [t log(t)]^{(1+ε)/2} / δ}` (p.11).

The `t` arrivals of periods `1, …, t` are i.i.d. from `p`; `DLP = σ(p, 0)` and
`EDLP(t) = σ(N(t)/t, 0)` are the selected solutions (Assumption 2) of `min_{x≥0} f_p(x)` and
`min_x f_{N(t)/t}(x)`.

**Formalization Note**
1. The second clause has the bound `[t log(t)]^{(1+ε)/2} / t` (reading). The printed bound is
   `≥ 1` for `t ≥ 2`, while both solutions have entries in `[0, 1]`; the threshold of Algorithm 1,
   `[log t]^{(1+ε)/2} / t^{(1−ε)/2}` (p.12), is exactly `[t log t]^{(1+ε)/2} / t`.
2. At `t = 2` the lemma is stated for `ε ≤ 1/2` (reading); every other `t ≥ 1` is stated for every
   `ε > 0`. The `ε` of the paper is that of Assumption 3 (p.8), and `T − T̂ > T^{1/2+ε}` forces
   `ε < 1/2` for every `T ≥ 2`, so no case of the paper is excluded. Without this restriction the
   case `t = 2` fails for large `ε`: `k = 2`, `ℓ = 1`, `f ≡ 0`, `σ(N, y)_θ = N_θ`,
   `p = (0.18, 0.82)`, `ε = 2`, `δ = 1`. Then `N(2) = (2, 0)` has probability `0.0324`, is a bad
   event (`|2 − 0.36| = 1.64 > (2 log 2)^{3/2} ≈ 1.632`) and gives `|DLP_11 − EDLP(2)_11| = 0.82 >
   (2 log 2)^{3/2}/2 ≈ 0.816`, while `2k t^{−2t^ε/δ²} = 4 · 2^{−8} ≈ 0.0156`.
3. Only the first `t` arrivals matter, so the probability is over `Fin t → Fin k` and
   `N_θ(t)` is `countAll`. `max_θ a_θ > c` is written `∃ θ, c < a_θ`. -/
theorem lemma_3_3 {k ℓ r m : ℕ} (I : Instance k ℓ r m)
    (σ : (Fin k → ℝ) → (Fin k → Fin ℓ → ℝ) → (Fin k → Fin ℓ → ℝ)) (δ ε : ℝ) (hδ : 0 < δ)
    (hε : 0 < ε) (hsel : Selection I σ δ) (p : Fin k → ℝ) (hp0 : ∀ θ, 0 ≤ p θ)
    (hp1 : ∑ θ, p θ = 1) (t : ℕ) (ht : 1 ≤ t) (ht2 : t = 2 → ε ≤ 1 / 2) :
    seqProb p (fun θs : Fin t → Fin k => ∃ θ,
        ((t : ℝ) * Real.log t) ^ ((1 + ε) / 2) / δ < |(countAll θs θ : ℝ) - t * p θ|) <
      2 * k * (t : ℝ) ^ (-(2 * (t : ℝ) ^ ε / δ ^ 2)) ∧
    1 - 2 * k * (t : ℝ) ^ (-(2 * (t : ℝ) ^ ε / δ ^ 2)) ≤
      seqProb p (fun θs : Fin t → Fin k => ∀ θ j,
        |σ p 0 θ j - σ (fun θ' => (countAll θs θ' : ℝ) / t) 0 θ j| <
          ((t : ℝ) * Real.log t) ^ ((1 + ε) / 2) / t) := by sorry

end GoodProphets
