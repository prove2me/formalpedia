-- Prove2me | Theorems.Thm_IntroDelayAMDP_Supplement_theorem_5_2
-- name    : IntroDelayAMDP.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:57:58.775782+00:00
-- url     : https://prove2.me/theorems/d11c3b72-3b6d-425d-820c-63204fa3f8bb
-- title:
--   Theorem 5.2 — Algorithm 5 has $\tilde O(d^3H^4\sqrt K+d^{3/2}H^3\sqrt D)$ regret in delayed linear AMDPs
-- statement:
--   Consider **delayed linear AMDPs**: linear AMDPs (Definition 2.1) on an arbitrary measurable, possibly uncountable, layered state space with $A$ actions, dimension $d$ and horizon $H$, together with delays $d_1,\dots,d_K\in\mathbb N$ fixed in advance (Definition 2.2), total delay $D=\sum_kd_k$ known, and $\sqrt K$ an integer. Run **Algorithm 5** with the cap $\bar d=\lceil\sqrt{D/(dH^2)}\rceil$ and the parameters of App. B.1 with this $\bar d$; in particular $\eta=1/(200H^3(\sqrt K+2\bar d)(\nu+4))$.
--
--   There is $\underline C$ such that for every $C\ge\underline C$ there is $\underline C_0$ such that for every $C_0\ge\underline C_0$ there are an absolute constant $c>0$ and an exponent $q\in\mathbb N$ such that, for every delayed linear AMDP, every $\delta\in(0,1/2)$, every removal rule of Algorithm 2, every fixed fallback policy and every probability space carrying the run, with probability at least $1-\delta$, simultaneously for every measurable policy $\pi$,
--   $$R_K(\pi)\le c\,\bigl(1+\log(KdHA/\delta)\bigr)^q\bigl(d^3H^4\sqrt K+d^{3/2}H^3\sqrt D\bigr).$$
--
--   The bound is optimal in $K$ and $D$ up to factors polynomial in $d$, $H$ and logarithms.
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
--   - encoding: d̄ = ⌈√(D/(dH²))⌉, η = Θ̃(1/(dH³(√K + d̄))) (see Lemma B.1), λ, m₀, ν, θ as in Theorem 4.1 → linParams C C₀ d̄ d H A K √K δ with d̄ = Nat.ceil √(D/(dH²)), ∃ C̲ ∀ C ≥ C̲ ∃ C̲₀ ∀ C₀ ≥ C̲₀; reason: the formal parameters of App. B.1 with the delay cap; C₁ occurs only in the proof
--   - encoding: delays d_1, …, d_K, D = Σ_k d_k, episode κ processed at the end of episode κ + min{d_κ, d̄} → 0-based delays dl : ℕ → ℕ, D = Σ_{k<K} dl k, processing times κ + min{dl κ, d̄}; every D ≥ 0 allowed; reason: Lean indexing; D = 0 (Algorithm 3) and D ≥ K² are covered as on the page
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Theorem 5.2, p.21; App. B.1, p.44; Algorithm 5, p.59; App. C.1, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_Supplement_IsLinearAMDP
import Definitions.Def_IntroDelayAMDP_Supplement_regretLin
import Definitions.Def_IntroDelayAMDP_Supplement_linParams__05dfee
import Definitions.Def_IntroDelayAMDP_Supplement_alg5Policy
import Definitions.Def_IntroDelayAMDP_Supplement_IsLinRealization

namespace IntroDelayAMDP.Supplement

open MeasureTheory ProbabilityTheory

/-- **Theorem 5.2** (printed p.21, PDF p.23) of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530):
"For delayed linear AMDPs and any `δ ∈ (0, 1/2)`, pick `d̄ = ⌈√(D/(dH²))⌉`, `η = Θ̃(1/(dH³(√K + d̄)))` (see
Lemma B.1), and `λ, m₀, ν, θ` as in Theorem 4.1. Then Algorithm 5 ensures the following with probability at
least `1 − δ`: `R_K = Õ(d³H⁴√K + d^{3/2}H³√D)`."
Delayed AMDPs (Definition 2.2, printed p.13): delays `d₁, …, d_K ≥ 0` fixed in advance by the oblivious
adversary, `D = ∑_k d_k` known to the algorithm.

There is `C̲` such that for every `C ≥ C̲` there is `C̲₀` such that for every `C₀ ≥ C̲₀` there are an absolute
constant `c > 0` and an exponent `q` with: for every linear AMDP on any measurable state space, every
nonempty finite action set, `d`, `H`, `ζ`, `ℓ`, every sequence of delays `d_k ∈ ℕ`, every `K = (√K)² ≥ 1`, every
`δ ∈ (0, 1/2)`, every removal rule, every measurable fixed policy, and every probability space carrying the
run of Algorithm 5 with the cap `d̄ = ⌈√(D/(dH²))⌉`, `D = ∑_{k<K} d_k`, and the parameters
`linParams C C₀ d̄ d H A K √K δ` of App. B.1,
`Pr[∃ measurable policy π, R_K(π) > c(1 + log(KdHA/δ))^q (d³H⁴√K + d^{3/2}H³√D)] ≤ δ`.

**Formalization Note.** As for Theorem 4.1: `Õ` is `c(1 + log(KdHA/δ))^q` with `c, q` chosen after the
parameter constants; `K = (√K)²`; comparators are the measurable policies; the law of the run is stated for
every probability space realizing the protocol, where episode `κ` is processed at the end of episode
`κ + min{d_κ, d̄}` (`tp`). The delays `dl k` belong to the 0-based episodes `k` (the paper's `d_{k+1}`), `D` sums
them over the `K` episodes, and every `D` is allowed (`D = 0` gives Algorithm 3; `D ≥ K²` makes the claim
trivial on the page). `d̄ = Nat.ceil √(D/(dH²))`, the root over the whole quotient. `d^{3/2}` is `Real.rpow`. -/
theorem theorem_5_2 :
    ∃ Clow : ℝ, ∀ C ≥ Clow, ∃ C0low : ℝ, ∀ C0 ≥ C0low, ∃ c > (0 : ℝ), ∃ q : ℕ,
      ∀ (X A : Type) [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
        [Fintype A] [Nonempty A] (d H K sqrtK : ℕ) (L : LayeredSpace X H) (P : A → Kernel X X)
        (φ : X → A → Fin d → ℝ) (ψ : Fin d → SignedMeasure X) (ζ : ℕ → ℕ → Fin d → ℝ)
        (ℓ : ℕ → X → A → ℝ), IsLinearAMDP L P φ ψ ζ ℓ K → K = sqrtK ^ 2 → 1 ≤ K →
      ∀ dl : ℕ → ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∀ (rule : RemovalRule d) (πfix : X → A → ℝ), IsPolicy πfix →
        (∀ a, Measurable fun s => πfix s a) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (traj : ℕ → ℕ → Ω → X × A)
        (coin : ℕ → ℕ → ℕ → Ω → ℝ),
        IsLinRealization μ L P K
          (fun κ => κ + min (dl κ)
            ⌈Real.sqrt ((∑ k ∈ Finset.range K, (dl k : ℝ)) / ((d : ℝ) * (H : ℝ) ^ 2))⌉₊) traj coin
          (fun ω => alg5Policy L φ ℓ
            (linParams C C0
              ⌈Real.sqrt ((∑ k ∈ Finset.range K, (dl k : ℝ)) / ((d : ℝ) * (H : ℝ) ^ 2))⌉₊
              d H (Fintype.card A) K sqrtK δ) rule K sqrtK
            ⌈Real.sqrt ((∑ k ∈ Finset.range K, (dl k : ℝ)) / ((d : ℝ) * (H : ℝ) ^ 2))⌉₊ dl
            πfix (fun t h => traj t h ω) (fun κ k h => coin κ k h ω)) →
        μ {ω | ∃ π : X → A → ℝ, IsPolicy π ∧ (∀ a, Measurable fun s => π s a) ∧
            c * (1 + Real.log ((K : ℝ) * d * H * (Fintype.card A : ℝ) / δ)) ^ q *
                ((d : ℝ) ^ 3 * (H : ℝ) ^ 4 * (sqrtK : ℝ) +
                  (d : ℝ) ^ (3 / 2 : ℝ) * (H : ℝ) ^ 3 * Real.sqrt (∑ k ∈ Finset.range K, (dl k : ℝ))) <
              regretLin L P ℓ
                (alg5Policy L φ ℓ
                  (linParams C C0
                    ⌈Real.sqrt ((∑ k ∈ Finset.range K, (dl k : ℝ)) / ((d : ℝ) * (H : ℝ) ^ 2))⌉₊
                    d H (Fintype.card A) K sqrtK δ) rule K sqrtK
                  ⌈Real.sqrt ((∑ k ∈ Finset.range K, (dl k : ℝ)) / ((d : ℝ) * (H : ℝ) ^ 2))⌉₊ dl
                  πfix (fun t h => traj t h ω) (fun κ k h => coin κ k h ω)) π K}
          ≤ ENNReal.ofReal δ := by sorry

end IntroDelayAMDP.Supplement
