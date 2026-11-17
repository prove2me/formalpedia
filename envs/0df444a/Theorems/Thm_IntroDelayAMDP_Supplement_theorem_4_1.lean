-- Prove2me | Theorems.Thm_IntroDelayAMDP_Supplement_theorem_4_1
-- name    : IntroDelayAMDP.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:55:47.692011+00:00
-- url     : https://prove2.me/theorems/f240ee6c-3bda-4e2f-9358-17331206f7d8
-- title:
--   Theorem 4.1 — Algorithm 3 has $\tilde O(d^3H^4\sqrt K)$ regret in linear AMDPs with high probability
-- statement:
--   Consider **linear AMDPs** (Definition 2.1) on an arbitrary measurable, possibly uncountable, layered state space with $A$ actions, feature dimension $d$ and horizon $H$, played for $K$ episodes where $\sqrt K$ is an integer. Run **Algorithm 3** (policy optimization with matrix geometric resampling) with the parameters of App. B.1 and $\bar d=0$:
--   $$\lambda=(KdH)^{-C},\quad m_0=\lceil C_0\rho\iota\rceil,\quad\nu=\lceil C_0m_0\iota\rceil,\quad\eta=\frac1{200H^3\sqrt K(\nu+4)},\quad\theta=\frac{C_0}{\sqrt K}\bigl(\rho(d_{VC}\iota+\iota^2)+m_0^2\bigr),$$
--   with $\iota=\log(16KdHA/\delta)$, $\rho=2d\log(1+1/\lambda)$.
--
--   There is $\underline C$ such that for every $C\ge\underline C$ there is $\underline C_0$ such that for every $C_0\ge\underline C_0$ there are an absolute constant $c>0$ and an exponent $q\in\mathbb N$ with the following property. For every linear AMDP, every oblivious loss sequence, every $\delta\in(0,1/2)$, every choice of the removal rule of Algorithm 2 and of the fixed policy played when $\theta>1/2$ or $K<2\sqrt K$, and every probability space carrying the run, with probability at least $1-\delta$, simultaneously for every measurable policy $\pi$,
--   $$R_K(\pi)=\sum_{k=1}^K\bigl(V^{\pi_k}_k(s_0)-V^\pi_k(s_0)\bigr)\le c\,\bigl(1+\log(KdHA/\delta)\bigr)^q\,d^3H^4\sqrt K.$$
--
--   That is, $R_K=\tilde O(d^3H^4\sqrt K)$ with high probability: the first bound for adversarial linear MDPs with bandit feedback and unknown transitions that is optimal in $K$, with no simulator.
--
--   **Formalization Note** The theorem's last sentence, "Moreover, Algorithm 3 is computationally efficient", is not formalized: the paper fixes no model of computation and states no running-time bound. The law of the run is stated for every probability space that carries the protocol, so the statement is about the law of Algorithm 3's interaction. Algorithm 3 is Algorithm 5 without delays (App. C.1).
--
--   Differences from the source:
--   - encoding: Õ(·) hides factors polylogarithmic in S, A, H, K, d and 1/δ → a factor c(1 + log(KdHA/δ))^q with an absolute c > 0 and q ∈ ℕ chosen after the parameter constants and before the instance; reason: S may be infinite, and App. B.1 itself uses ι = log(16KdHA/δ); this is the reading of the published goal IntroDelayAMDP.theorem_3_1
--   - encoding: for simplicity, √K is an integer (p.17) → K = sqrtK² with sqrtK the integer √K; reason: the standing assumption of Section 4, stated as a hypothesis
--   - encoding: R_K against π⋆ ∈ argmin over all policies Π → the regret against every measurable Markov policy, bounded on one event; reason: π⋆ is deterministic (oblivious losses), and V^π is defined through integrals only for measurable π
--   - encoding: "with probability at least 1 − δ" over the interaction (Section 2.1) → μ of the failure set ≤ δ for every probability space (Ω, μ) carrying the run (IsLinRealization); reason: the claim is about the law of the run, which every such space carries; such spaces exist (Ionescu-Tulcea)
--   - encoding: Algorithm 2, line 5: "remove one such i" → every RemovalRule, universally quantified; reason: the page does not fix the choice
--   - encoding: "the agent plays a fixed policy" if θ > 1/2 or K < 2√K → every measurable fixed policy πfix, universally quantified; reason: the page does not fix the policy
--   - encoding: Σ̂_j^{-1/2} = square root of the Moore–Penrose pseudo-inverse; eigenvalue truncation (Algorithm 2, line 8) → continuous functional calculus cfc (x ↦ (√x)⁻¹) and cfc (x ↦ if x < λm_j/|R_j| then 0 else x) of the symmetric matrices; reason: the spectral definitions of the same matrices
--   - encoding: an estimate makes one attempt with each of the next M_j − 1 episodes and finishes when n = M_j − 1 → the estimate starts unfinished iff M_j ≥ 2 and finishes when n + 1 = M_j; reason: identical for M_j ≥ 2, and M_j ≥ m₀ ≥ 2 for the App. B.1 parameters once C₀ ≥ 1, which the constant C̲₀ may assume
--   - encoding: linear AMDP with d-dimensional features, K episodes of H steps, ‖·‖₂ bounds, features and layers measurable (convention) → IsLinearAMDP with squared norms and measurability of the layer map and of φ(·, a); any d, H ∈ ℕ; 0-based episodes; no terminal layer; reason: same instances; for d = 0 or H = 0 all losses and values vanish, the regret is 0 and the claim holds trivially
--   - encoding: λ = (KdH)^{-C} "for a large enough universal constant C", m₀, ν = Θ̃(d), η, θ (Lemma B.1: "C₁, C, and C₀ … each large enough given the previous ones") → linParams C C₀ 0 d H A K √K δ with ∃ C̲ ∀ C ≥ C̲ ∃ C̲₀ ∀ C₀ ≥ C̲₀; reason: the formal parameters of App. B.1; C₁ occurs only in the proof
--   - encoding: Algorithm 3 → Algorithm 5 with all delays 0 and d̄ = 0 (alg3Policy); reason: App. C.1: "Without delays, we have d̄ = 0, and Algorithms 4 and 5 are exactly Algorithms 1 and 3"; the skip window is √K < κ ≤ K − √K
--   - reading: "Moreover, Algorithm 3 is computationally efficient." → not stated; reason: an informal remark: the paper names no model of computation and no running-time bound (its justification, p.20, is prose), so it has no formal content to state; the regret clause is stated in full
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Theorem 4.1, p.20; App. B.1, p.44

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_Supplement_IsLinearAMDP
import Definitions.Def_IntroDelayAMDP_Supplement_regretLin
import Definitions.Def_IntroDelayAMDP_Supplement_linParams__05dfee
import Definitions.Def_IntroDelayAMDP_Supplement_alg3Policy
import Definitions.Def_IntroDelayAMDP_Supplement_IsLinRealization

namespace IntroDelayAMDP.Supplement

open MeasureTheory ProbabilityTheory

/-- **Theorem 4.1** (printed p.20, PDF p.22) of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530):
"For linear AMDPs and any `δ ∈ (0, 1/2)`, pick `λ = (KdH)^{−C}` for a large enough universal constant `C`, let
`m₀, ν = Θ̃(d)`, `η = Θ̃(1/(dH³√K))`, and `θ = Θ̃(d³/√K)`. Then Algorithm 3 ensures the following with
probability at least `1 − δ`: `R_K = Õ(d³H⁴√K)`. Moreover, Algorithm 3 is computationally efficient."
The parameters are those of App. B.1 (printed p.44, "see Lemma B.1 for the formal definitions"): "Let `C₁`,
`C`, and `C₀` be universal constants, each large enough given the previous ones".

There is `C̲` such that for every `C ≥ C̲` there is `C̲₀` such that for every `C₀ ≥ C̲₀` there are an absolute
constant `c > 0` and an exponent `q` with: for every linear AMDP (Definition 2.1) on any measurable state
space `X` (finite, countable or uncountable), any nonempty finite action set of size `A`, any feature dimension
`d`, horizon `H`, loss vectors `ζ` and losses `ℓ`, every `K = (√K)² ≥ 1`, every `δ ∈ (0, 1/2)`, every removal
rule of Algorithm 2, every measurable fixed policy `πfix` (played when `θ > 1/2` or `K < 2√K`), and every
probability space carrying the run of Algorithm 3 with the parameters `linParams C C₀ 0 d H A K √K δ`,
`Pr[∃ measurable policy π, R_K(π) > c(1 + log(KdHA/δ))^q d³H⁴√K] ≤ δ`,
where `R_K(π) = ∑_k (V^{π_k}_k(s₀) − V^π_k(s₀))`.

**Formalization Note.** `Õ`/`Θ̃` hide polylogarithmic factors in `S, A, H, K, d, 1/δ` (printed p.12); with
`S` possibly infinite, the factor is `c(1 + log(KdHA/δ))^q` (App. B.1 uses `ι = log(16KdHA/δ)`), with `c, q`
chosen after the parameter constants and before the instance. `C₁` occurs only in the proof, so the
constants of the algorithm are `C` then `C₀`. "For simplicity, we assume that `√K` is an integer"
(printed p.17): `K = (√K)²`. The clause "Moreover, Algorithm 3 is computationally efficient" is not
formalized: the paper fixes no model of computation and states no running-time bound, and the
definitions carry no notion of running time. The comparator `π⋆` is read as every measurable Markov policy
on one event (those are the policies with a defined `V^π`). The law of the run is stated by quantifying
over every probability space realizing the protocol (`IsLinRealization`); Algorithm 3 is Algorithm 5
without delays (App. C.1). Episodes are 0-based and there is no terminal layer. -/
theorem theorem_4_1 :
    ∃ Clow : ℝ, ∀ C ≥ Clow, ∃ C0low : ℝ, ∀ C0 ≥ C0low, ∃ c > (0 : ℝ), ∃ q : ℕ,
      ∀ (X A : Type) [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
        [Fintype A] [Nonempty A] (d H K sqrtK : ℕ) (L : LayeredSpace X H) (P : A → Kernel X X)
        (φ : X → A → Fin d → ℝ) (ψ : Fin d → SignedMeasure X) (ζ : ℕ → ℕ → Fin d → ℝ)
        (ℓ : ℕ → X → A → ℝ), IsLinearAMDP L P φ ψ ζ ℓ K → K = sqrtK ^ 2 → 1 ≤ K →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∀ (rule : RemovalRule d) (πfix : X → A → ℝ), IsPolicy πfix →
        (∀ a, Measurable fun s => πfix s a) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (traj : ℕ → ℕ → Ω → X × A)
        (coin : ℕ → ℕ → ℕ → Ω → ℝ),
        IsLinRealization μ L P K (fun κ => κ) traj coin
          (fun ω => alg3Policy L φ ℓ (linParams C C0 0 d H (Fintype.card A) K sqrtK δ) rule K sqrtK
            πfix (fun t h => traj t h ω) (fun κ k h => coin κ k h ω)) →
        μ {ω | ∃ π : X → A → ℝ, IsPolicy π ∧ (∀ a, Measurable fun s => π s a) ∧
            c * (1 + Real.log ((K : ℝ) * d * H * (Fintype.card A : ℝ) / δ)) ^ q *
                ((d : ℝ) ^ 3 * (H : ℝ) ^ 4 * (sqrtK : ℝ)) <
              regretLin L P ℓ
                (alg3Policy L φ ℓ (linParams C C0 0 d H (Fintype.card A) K sqrtK δ) rule K sqrtK
                  πfix (fun t h => traj t h ω) (fun κ k h => coin κ k h ω)) π K}
          ≤ ENNReal.ofReal δ := by sorry

end IntroDelayAMDP.Supplement
