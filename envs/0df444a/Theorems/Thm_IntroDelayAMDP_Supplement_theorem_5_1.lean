-- Prove2me | Theorems.Thm_IntroDelayAMDP_Supplement_theorem_5_1
-- name    : IntroDelayAMDP.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:56:43.516882+00:00
-- url     : https://prove2.me/theorems/d4afc0bc-6473-47ec-8d06-7e66b04b4670
-- title:
--   Theorem 5.1 — Algorithm 4 has $\tilde O(H^{5/2}\sqrt{SAK}+H^3\sqrt D+H^4S^2A)$ regret in delayed tabular AMDPs
-- statement:
--   Consider **tabular AMDPs with delayed feedback** (Definition 2.2): a layered finite state space with $S$ non-terminal states, $A$ actions, horizon $H$, an unknown transition $P$, losses $\ell_k\in[0,1]$ and delays $d_1,\dots,d_K\in\mathbb N$ chosen in advance by an oblivious adversary, with total delay $D=\sum_kd_k$ known to the learner; the losses of episode $k$ are revealed at the end of episode $k+d_k$. Run **Algorithm 4** with the cap $\bar d=\lceil\sqrt D/H\rceil$ and the parameters of Lemma A.2 (App. A.1) built from a universal constant $C$ and this $\bar d$.
--
--   There is $C_0$ such that for every $C\ge C_0$ there are an absolute constant $c>0$ and an exponent $q\in\mathbb N$ such that, for every tabular instance, every loss and delay sequence, every $K\ge1$ and every $\delta\in(0,1)$, with probability at least $1-\delta$, simultaneously for every policy $\pi$,
--   $$R_K(\pi)=\sum_{k=1}^K\bigl(V^{\pi_k}_k(s_0)-V^\pi_k(s_0)\bigr)\le c\,\bigl(1+\log(SAHK/\delta)\bigr)^q\bigl(H^{5/2}\sqrt{SAK}+H^3\sqrt D+H^4S^2A\bigr).$$
--
--   This is the formal version, Theorem C.3, of Theorem 5.1. It matches the $\Omega(H\sqrt{SAK}+H\sqrt D)$ lower bound in $S$, $A$, $K$ and $D$ up to factors of $H$ and logarithms.
--
--   **Formalization Note** The randomness is the base mission's uniform random tape; Algorithm 4 is a function of the tape (`alg4Policy`).
--
--   Differences from the source:
--   - encoding: Õ(·) hides factors polylogarithmic in S, A, H, K and 1/δ → a factor c(1 + log(SAHK/δ))^q with an absolute c > 0 and q ∈ ℕ chosen after C and before the instance; reason: the reading of the published goal IntroDelayAMDP.theorem_3_1
--   - encoding: d̄ = ⌈√D/H⌉, η = Θ̃(min{1/(H³(1 + d̄)), 1/(H^{3/2}√(SAK))}) and the other parameters as in Theorem 3.1 (Lemma A.2, "C a large enough universal constant") → tabParams C d̄ S A H K δ with d̄ = Nat.ceil (√D / H), ∃ C₀ ∀ C ≥ C₀; reason: the formal version, Theorem C.3, uses "the parameters in Lemma A.2", whose η carries d̄; the published tabParams is that record
--   - encoding: R_K against π⋆ ∈ argmin over all policies → the regret against every policy, bounded on one event; reason: π⋆ is deterministic (oblivious losses); as in the published goal
--   - encoding: probability over the interaction and the internal randomness → the product-uniform law of the base mission's random tape, Algorithm 4 a function of the tape; reason: the same joint law of trajectories and coins; as in the published goal
--   - encoding: episodes and delays d_1, …, d_K, D = Σ_k d_k, terminal layer S_H → 0-based episodes, delays dl : ℕ → ℕ with dl k the paper's d_{k+1}, D = Σ_{k<K} dl k, no terminal layer; every D ≥ 0 allowed; reason: Lean indexing; the published LayeredSpace has no terminal layer; D = 0 and D ≥ K² are covered as on the page
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Theorem 5.1, p.21; Theorem C.3, p.60; Algorithm 4, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_regret
import Definitions.Def_IntroDelayAMDP_Supplement_alg4Policy

namespace IntroDelayAMDP.Supplement

open MeasureTheory

/-- **Theorem 5.1** (printed p.21, PDF p.23), in its formal version **Theorem C.3** (printed p.60, PDF p.62),
of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530).
Theorem 5.1: "For tabular AMDPs with delayed feedback and any `δ ∈ (0, 1)`, pick `d̄ = ⌈√D/H⌉`,
`η = Θ̃(min{1/(H³(1 + d̄)), 1/(H^{3/2}√(SAK))})`, and the other parameters as in Theorem 3.1 (see Lemma A.2).
Then Algorithm 4 ensures the following with probability at least `1 − δ`:
`R_K = Õ(H^{5/2}√(SAK) + H³√D + H⁴S²A)`."
Theorem C.3: "With `d̄ = ⌈√D/H⌉` and the parameters in Lemma A.2, Algorithm 4 ensures
`R_K = Õ(H^{5/2}√(SAK) + H³√D + H⁴S²A)` with probability at least `1 − δ`."

There is `C₀` such that for every `C ≥ C₀` there are an absolute constant `c > 0` and an exponent `q` with:
for every tabular layered AMDP (finite non-terminal state set of size `S`, finite nonempty action set of
size `A`, any horizon `H`, any valid transition `P`), every loss sequence in `[0, 1]` and every sequence of
delays `d_k ∈ ℕ` (both fixed in advance), every `K ≥ 1` and every `δ ∈ (0, 1)`, Algorithm 4 with the cap
`d̄ = ⌈√D/H⌉`, `D = ∑_{k<K} d_k`, and the parameters `tabParams C d̄ S A H K δ` of App. A.1 satisfies
`Pr[∃ π, R_K(π) > c(1 + log(SAHK/δ))^q (H^{5/2}√(SAK) + H³√D + H⁴S²A)] ≤ δ`,
where `R_K(π) = ∑_k (V^{π_k}_k(s₀) − V^π_k(s₀))` is the regret against the policy `π`.

**Formalization Note.** `Õ(·)` hides polylogarithmic factors in `S, A, H, K, 1/δ` (p.12): it is read as the
factor `c(1 + log(SAHK/δ))^q` with `c, q` chosen after `C` and before the instance (as in the published
`IntroDelayAMDP.theorem_3_1`). "The parameters in Lemma A.2" are `tabParams C d̄ …` with "`C` a large enough
universal constant" read as `∀ C ≥ C₀`; that record already carries `d̄` in `η`. The delays `dl k` belong
to the 0-based episodes `k` (the paper's `d_{k+1}`), `D` sums them over the `K` episodes, and every `D`
(including `D = 0` and `D ≥ K²`) is allowed. `d̄` is `Nat.ceil (√D / H)`, the root over `D` only. The regret
against `π⋆` is the regret against every policy on one event. Episodes are 0-based, there is no terminal
layer, and the run is realized on the uniform random tape of the base mission. -/
theorem theorem_5_1 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ c > (0 : ℝ), ∃ q : ℕ,
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ dl : ℕ → ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      tapeMeasure St A K H {ω | ∃ π : St → A → ℝ, IsPolicy π ∧
          c * (1 + Real.log ((Fintype.card St : ℝ) * (Fintype.card A : ℝ) * H * K / δ)) ^ q *
              ((H : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt ((Fintype.card St : ℝ) * (Fintype.card A : ℝ) * K) +
                (H : ℝ) ^ 3 * Real.sqrt (∑ k ∈ Finset.range K, (dl k : ℝ)) +
                (H : ℝ) ^ 4 * (Fintype.card St : ℝ) ^ 2 * (Fintype.card A : ℝ)) <
            regret L P ℓ
              (alg4Policy L P ℓ
                (tabParams C ⌈Real.sqrt (∑ k ∈ Finset.range K, (dl k : ℝ)) / H⌉₊
                  (Fintype.card St) (Fintype.card A) H K δ)
                ⌈Real.sqrt (∑ k ∈ Finset.range K, (dl k : ℝ)) / H⌉₊ dl ω) π K}
        ≤ ENNReal.ofReal δ := by sorry

end IntroDelayAMDP.Supplement
