-- Prove2me | Theorems.Thm_IntroDelayAMDP_theorem_3_1
-- name    : IntroDelayAMDP.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:53:40.374186+00:00
-- url     : https://prove2.me/theorems/e2420c7e-8fc9-4f80-aa0a-998cafa4b745
-- title:
--   Theorem 3.1 / Theorem A.3 — Algorithm 1 has regret $\tilde O(H^{5/2}\sqrt{SAK}+H^4S^2A)$ with high probability
-- statement:
--   There is $C_0$ such that for every $C\ge C_0$ there are a constant $c>0$ and an exponent $q$ with the following property. For every tabular layered AMDP (finite non-terminal state set of size $S$, finite nonempty action set of size $A$, any horizon $H$, any transition $P$), every loss sequence in $[0,1]$ chosen in advance, every $K\ge1$ and every $\delta\in(0,1)$, Algorithm 1 with the parameters of App. A.1 for $C$ and $\bar d=0$ satisfies, with probability at least $1-\delta$, for every policy $\pi$,
--   $$R_K(\pi)\le c\,\bigl(1+\log(SAHK/\delta)\bigr)^q\bigl(H^{5/2}\sqrt{SAK}+H^4S^2A\bigr).$$
--
--   This is the paper's main theorem for tabular AMDPs. It improves the $\tilde O(H^2S\sqrt{AK})$ bound of Luo, Wei and Lee by a factor of $\sqrt{S/H}$, and gives an optimal dependence on $S$ and $K$ with bandit feedback and an unknown transition.
--
--   Differences from the source:
--   - reading: Õ(·), hiding factors polylogarithmic in S, A, H, K, 1/δ (p.12) → the factor c(1 + log(SAHK/δ))^q, with c and q chosen after C and before the instance, K and δ; reason: c may depend on C, as (29) shows; 1 + log is at least 1, so the factor is a genuine polylogarithm
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - encoding: R_K against π⋆ ∈ argmin_π Σ_k V^π_k(s₀) → the bound against every policy on one event; reason: π⋆ is deterministic for oblivious losses and is pointwise worst, so the two are equivalent
--   - encoding: pick ν = Θ(log²(SAHK/δ)), c₁ = Θ(ν), θ = Θ̃(ηH³), M = Θ̃(1/θ), η = Θ̃(min{1/H³, 1/(H^{3/2}√(SAK))}), with the constants in Lemma A.2 → the explicit parameters of App. A.1, with d̄ = 0; reason: Theorem A.3 and the printed "with the constants in Lemma A.2" fix these values
--   - encoding: with probability at least 1 − p → μ(failure set) ≤ p; reason: outer-measure bound on the failure set; no measurability side condition is needed
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Theorem 3.1, p.15; Theorem A.3, p.31; parameters, App. A.1, p.30

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_regret

namespace IntroDelayAMDP

open MeasureTheory

/-- **Theorem 3.1** (printed p.15), in its formal version **Theorem A.3** (printed p.31), of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530).
Theorem 3.1: "For tabular AMDPs and any `δ ∈ (0, 1)`, pick `ν = Θ(log²(SAHK/δ))`, `c₁ = Θ(ν)`, `γ = ηH²`,
`θ = Θ̃(ηH³)`, `M = Θ̃(1/θ)`, and `η = Θ̃(min{1/H³, 1/(H^{3/2}√(SAK))})`, with the constants in Lemma A.2.
Then Algorithm 1 ensures the following with probability at least `1 − δ`: `R_K = Õ(H^{5/2}√(SAK) + H⁴S²A)`."
Theorem A.3: "With the parameters in Lemma A.2, Algorithm 1 ensures `R_K = Õ(H^{5/2}√(SAK) + H⁴S²A)` with
probability at least `1 − δ`."

There is `C₀` such that for every `C ≥ C₀` there are an absolute constant `c > 0` and an exponent `q`
with: for every tabular layered AMDP (finite non-terminal state set of size `S`, finite nonempty action
set of size `A`, any horizon `H`, any valid transition `P`), every loss sequence in `[0, 1]` (fixed in
advance), every `K ≥ 1` and every `δ ∈ (0, 1)`, Algorithm 1 with the parameters `tabParams C 0 S A H K δ`
of App. A.1 satisfies
`Pr[∃ π, R_K(π) > c(1 + log(SAHK/δ))^q (H^{5/2}√(SAK) + H⁴S²A)] ≤ δ`,
where `R_K(π) = ∑_k (V^{π_k}_k(s₀) − V^π_k(s₀))` is the regret against the policy `π`.

**Formalization Note.** `Õ(·)` hides polylogarithmic factors in `S, A, H, K, 1/δ` (p.12): it is read as
the factor `c(1 + log(SAHK/δ))^q` with `c, q` chosen after `C` and before the instance. "`C` a large
enough universal constant" is read as `∀ C ≥ C₀`. The regret against the optimal policy in hindsight
`π⋆` is the regret against every policy on one event (`π⋆` is deterministic for oblivious losses).
Episodes are 0-based, there is no terminal layer, and the run is realized on a uniform random tape. -/
theorem theorem_3_1 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ c > (0 : ℝ), ∃ q : ℕ,
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      tapeMeasure St A K H {ω | ∃ π : St → A → ℝ, IsPolicy π ∧
          c * (1 + Real.log ((Fintype.card St : ℝ) * (Fintype.card A : ℝ) * H * K / δ)) ^ q *
              ((H : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt ((Fintype.card St : ℝ) * (Fintype.card A : ℝ) * K) +
                (H : ℝ) ^ 4 * (Fintype.card St : ℝ) ^ 2 * (Fintype.card A : ℝ)) <
            regret L P ℓ
              (alg1Policy L P ℓ (tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ) ω) π K}
        ≤ ENNReal.ofReal δ := by sorry

end IntroDelayAMDP
