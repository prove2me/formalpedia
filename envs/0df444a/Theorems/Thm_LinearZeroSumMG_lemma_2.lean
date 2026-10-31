-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_2
-- name    : LinearZeroSumMG.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:55:06.877423+00:00
-- url     : https://prove2.me/theorems/47541177-9272-4a66-ac1f-b92bb2e0a200
-- title:
--   Lemma 2, p.17 — the concentration event $\mathfrak E$ holds with probability at least $1-p/2$
-- statement:
--   **Lemma 2 (Concentration).** There is a universal constant $C_2>0$ such that for every $c\ge2$ the following holds. Let $d,K,H\ge1$, let the game satisfy Assumption 1, let $p\in(0,1)$, and run Algorithm 1 for $K$ episodes with
--   - $\beta=c\,dH\sqrt\iota$, $\iota=\log(2dT/p)$, $T=KH$;
--   - a measurable CCE rule;
--   - for each episode $k\in[K]$, an $\varepsilon$-net of minimum size of the class $\mathcal Q$ of (5), with $\varepsilon=1/(KH)$, and an admissible rounding rule into these nets;
--   - adaptively chosen initial states.
--
--   Then, with probability at least $1-p/2$, for all $(k,h)\in[K]\times[H]$,
--   $$
--   \Big\|\sum_{\tau=1}^{k-1}\phi^\tau_h\Big[\overline V^k_{h+1}(x^\tau_{h+1})-(\mathbb P_h\overline V^k_{h+1})(x^\tau_h,a^\tau_h,b^\tau_h)\Big]\Big\|_{(\Lambda^k_h)^{-1}}\le C_2\sqrt{1+\log c}\;dH\sqrt{\log(dT/p)},
--   $$
--   and the same with $\underline V^k_{h+1}$. That is, the event $\mathfrak E(C_2\sqrt{1+\log c})$ holds with probability at least $1-p/2$.
--
--   The difficulty is that $\overline V^k_{h+1}$ depends on the same past data as the features; the rounding into a finite net is what allows a union bound. The bound feeds the least-squares error bound (Lemma 3).
--
--   Differences from the source:
--   - reading: "≲ dH√(log(dT/p))" under the setting of Theorem 1 (β = c·dH√ι with Theorem 1's c) → ∃ universal C₂ > 0, for every c ≥ 2, the bound C₂√(1 + log c)·dH√(log(dT/p)); reason: the constant of ≲ depends on c through the net size, log 𝒩_ε ≲ d²(ι + log c) (via β²); making the dependence explicit lets Lemmas 3, 5, 6 take c large relative to it; c ≥ 2 gives β ≥ 1, needed for the estimates to lie in 𝒬; fixing c recovers the printed statement
--   - reading: Assumption 1's normalization ‖μ_h(𝒮)‖ ≤ √d (p.7) → ‖(∫ v dμ_h^{(i)})_{i∈[d]}‖ ≤ √d for every measurable v : 𝒮 → [−1, 1] (IsLinearMG); reason: read literally as a bound on the vector of net masses, the assumption does not give ‖∫ V dμ_h‖ ≤ H√d for |V| ≤ H, which the proofs of Lemmas 3 and 7 use, and Lemma 7 is then false (d = 3, two states, φ(s) = (0.7, 0.5, 0), φ(t) = (0.7, −0.5, 0), μ = ((δ_s+δ_t)/1.4, δ_s − δ_t, 7(δ_s − δ_t)), θ = (0, 1, 0), H = 2: ‖μ(𝒮)‖ ≈ 1.43 ≤ √3 but ‖w_1‖ ≥ 7 > 4√3); the reading implies the printed bound (v ≡ 1) and is implied by the total-variation bound
--   - reading: "let σ̃(x) be the CCE" (Algorithm 2, line 3, p.11) → every Borel-measurable rule cce mapping a pair of payoff matrices to one of its CCEs (IsCCERule), fixed in advance; reason: the definite article and Lemma 2's proof ("Fix a pair (Q̃, Q̰) in the ε-net … let σ̃(x) be the CCE") require a rule fixed before the run; the statement holds for every such rule
--   - reading: "Pick a pair (Q̃, Q̰) in 𝒬_ε × 𝒬_ε satisfying ‖Q̃ − Q̄^k_h‖_∞ ≤ ε and ‖Q̰ − Q̲^k_h‖_∞ ≤ ε" (Algorithm 2, line 2, p.11) → every measurable rounding rule that, given k, h and the parameters (w̄^k_h, (Λ^k_h)⁻¹), (w̲^k_h, (Λ^k_h)⁻¹) of Q̄^k_h and Q̲^k_h, returns such a pair whenever both lie in 𝒬 (IsRoundingRule); reason: "pick" allows any qualifying pair; one pair must serve every state x (Lemma 2's proof rounds Q̄^k_{h+1} once); any choice that is a function of FIND_CCE's input pair is such a rule
--   - reading: "Let 𝒬_ε be a fixed ε-covering of 𝒬" (p.11) → for each episode k ∈ [K], an ε-net of the class 𝒬 of (5) for that k (‖w‖ ≤ 2H√(dk)), contained in 𝒬 and of minimum cardinality (IsMinEpsNet); reason: Lemma 2's proof uses |𝒬_ε × 𝒬_ε| = (𝒩_ε)², the covering number; an arbitrary cover (e.g. 𝒬 itself) breaks the union bound; 𝒬 depends on k through ‖w‖ ≤ 2H√(dk)
--   - generalization: "an arbitrary initial state x^k_1 is chosen" (p.9) → x^k_1 is any random state measurable with respect to everything observed before episode k (IsOmniRun); reason: an adaptively chosen initial state covers every fixed sequence of initial states
--   - encoding: feature map, policies, CCE rule and rounding with no measurability stated; finite action set → φ jointly measurable, policies measurable in the state, CCE rule and rounding rule Borel measurable, A with its discrete σ-algebra; reason: without measurability the expectations ℙ_h V and the conditional laws of the analysis are undefined; these conditions exclude only such cases
--   - encoding: d, K, H the feature dimension, number of episodes and horizon → 1 ≤ d, 1 ≤ K, 1 ≤ H as hypotheses; reason: ι = log(2dT/p), ε = 1/(KH) and 8/K are undefined otherwise; nondegeneracy only
--   - encoding: "with probability at least 1 − p" → the outer measure of the set of sample points where the bound fails is at most p; reason: no measurability of the event is needed; same statement when it is measurable
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 2, p.17; proof, pp.17–18

import Mathlib
import Definitions.Def_LinearZeroSumMG_IsLinearMG
import Definitions.Def_LinearZeroSumMG_IsEpsNet
import Definitions.Def_LinearZeroSumMG_IsOmniRun
import Definitions.Def_LinearZeroSumMG_concEvent
import Definitions.Def_LinearZeroSumMG_iota

open MeasureTheory ProbabilityTheory

namespace LinearZeroSumMG

/-- **Lemma 2 (Concentration).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 2, p.17: "Under the setting of
Theorem 1, for each `p ∈ (0, 1)`, the following event `𝔈` holds with probability at least `1 − p/2`:
`‖∑_{τ∈[k−1]} φ^τ_h [V̄^k_{h+1}(x^τ_{h+1}) − (ℙ_h V̄^k_{h+1})(x^τ_h, a^τ_h, b^τ_h)]‖_{(Λ^k_h)⁻¹} ≲ dH√(log(dT/p))`, `∀(k, h) ∈ [K] × [H]`,
`‖∑_{τ∈[k−1]} φ^τ_h [V̲^k_{h+1}(x^τ_{h+1}) − (ℙ_h V̲^k_{h+1})(x^τ_h, a^τ_h, b^τ_h)]‖_{(Λ^k_h)⁻¹} ≲ dH√(log(dT/p))`, `∀(k, h) ∈ [K] × [H]`."

There is a universal constant `C₂ > 0` such that for every `c ≥ 2` the following holds. Take any
`d, K, H ≥ 1`, any game satisfying Assumption 1, any `p ∈ (0, 1)`, any measurable CCE rule, any
family of minimum-size `ε`-nets `𝒬_ε` of the classes `𝒬` (episodes `k ∈ [1, K]`), any rounding rule,
with `β = c·dH√ι`, `ι = log(2dT/p)`, `T = KH` and `ε = 1/(KH)`, and any run of Algorithm 1 for `K`
episodes. Then the outer probability that the event `𝔈` fails with constant `C₂√(1 + log c)` is at
most `p/2`.

**Formalization Note**
- The `≲` of the event is made explicit as `C₂√(1 + log c)`: the union bound over the net gives
  `log |𝒬_ε × 𝒬_ε| ≲ d²(ι + log c)` (through `β²`), so the constant of `𝔈` may grow with `c`, but only
  like `√(1 + log c)`. This lets Lemmas 3, 5 and 6 choose `c` after `C₂`; specializing `c` to a fixed
  value gives the printed statement.
- `c ≥ 2` gives `β ≥ 1`, so that the algorithm's `Q̄^k_h`, `Q̲^k_h` lie in `𝒬` and the rounding is
  `ε`-close.
- "With probability at least `1 − p/2`" bounds the outer measure of the failure set by `p/2`. -/
theorem lemma_2 :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ c : ℝ, 2 ≤ c →
    ∀ {S A : Type} [MeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]
      [Fintype A] [Nonempty A] (d K : ℕ) (G : MarkovGame S A) (φ : S → A → A → Fin d → ℝ)
      (θ : ℕ → Fin d → ℝ) (μh : ℕ → Fin d → SignedMeasure S) (p : ℝ)
      (cce : (A → A → ℝ) → (A → A → ℝ) → (A × A → ℝ)) (N : ℕ → Finset (S → A → A → ℝ))
      (round : RoundRule S A d) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (x : ℕ → ℕ → Ω → S)
      (a b : ℕ → ℕ → Ω → A),
      1 ≤ d → 1 ≤ K → 1 ≤ G.H → IsLinearMG G φ θ μh → 0 < p → p < 1 → IsCCERule cce →
      (∀ k ∈ Finset.Icc 1 K, IsMinEpsNet (N k)
        (QClass φ G.H (c * d * G.H * Real.sqrt (iota d K G.H p)) k) (1 / ((K : ℝ) * G.H))) →
      IsRoundingRule φ G.H (c * d * G.H * Real.sqrt (iota d K G.H p)) (1 / ((K : ℝ) * G.H))
        N K round →
      IsOmniRun μ 𝓕 G ⟨φ, c * d * G.H * Real.sqrt (iota d K G.H p), cce, round⟩ K x a b →
      μ {ω | ¬ concEvent G ⟨φ, c * d * G.H * Real.sqrt (iota d K G.H p), cce, round⟩ K p
          (C₂ * Real.sqrt (1 + Real.log c))
          (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω)}
        ≤ ENNReal.ofReal (p / 2) := by sorry

end LinearZeroSumMG
