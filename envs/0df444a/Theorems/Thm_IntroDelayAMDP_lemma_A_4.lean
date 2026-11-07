-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_4
-- name    : IntroDelayAMDP.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:39.824224+00:00
-- url     : https://prove2.me/theorems/7f2da0c2-0e3c-4cda-abd5-5babc15c8fbc
-- title:
--   Lemma A.4 — GRR guarantee, general version
-- statement:
--   On a probability space with a sub-σ-algebra $\mathcal G$, let $\pi_k,\pi_\kappa$ be $\mathcal G$-measurable random policies, and let $\tau$ be the first $h+1$ steps of an episode whose conditional law given $\mathcal G$ is that of a trajectory of $\pi_\kappa$ under $P$. Let $A_\kappa\in\{0,1\}$ have conditional mean $\alpha_{k,\kappa}(\tau)\in[0,1]$ given $\mathcal G$ and $\tau$. Then every bounded $f$ that is $\mathcal G$-measurable in its sample-point argument satisfies, almost surely,
--   $$\mathbb E[A_\kappa f(\tau)\mid\mathcal G]=\frac12\mathbb E^{\pi_k}[f(\tau^h)].$$
--   This is the guarantee of geometric resampling with rejection: an accepted episode looks like half a trajectory of the older policy. The paper also uses it in Appendices B and C, so it is stated in its generality.
--
--   **Formalization Note** $\mathbb E^{\pi_k}[f(\tau^h)]$ is the finite sum over partial trajectories with the trajectory probability.
--
--   Differences from the source:
--   - reading: episode κ is accepted with probability α_{k,κ} independently → the conditional mean of A_κ given 𝒢 and τ is α_{k,κ}(τ); reason: the proof's display is exactly this use of independence
--   - reading: α_{k,κ} ∈ [0, 1], with the ratio of (4) written without restriction → the added hypothesis π_κ(a|s) = 0 → π_k(a|s) = 0; reason: it makes the ratio meaningful (x/0 = 0 in Lean); it holds for the positive policies of the paper
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.4, p.32

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_accProb
import Definitions.Def_IntroDelayAMDP_trajProb

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.4 (GRR Guarantee; General Version)** (printed p.32, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "Let `π_k` and `π_κ` be
fixed given a σ-algebra `G`, given which episode `κ` follows `π_κ`. If episode `κ` is accepted
(`A_κ = 1`) with probability `α_{k,κ} ∈ [0, 1]` independently, then every bounded `f` fixed given `G`
satisfies `E[A_κ f(τ^h_κ) | G] = ½ E^{π_k}[f(τ^h)]`. (30)"

Setting: a probability space `(Ω, μ)`, a sub-σ-algebra `𝒢`, a layer `h < H`, `𝒢`-measurable random
policies `π_k, π_κ`, and the first `h + 1` steps `τ = τ^h_κ` of episode `κ`, whose conditional law
given `𝒢` is that of a trajectory of `π_κ` under `P`. The acceptance indicator `A_κ ∈ {0, 1}` has
conditional mean `α_{k,κ}(τ)` of (4) given `𝒢` and `τ`, and `α_{k,κ} ∈ [0, 1]`. Then for every bounded
`f(ω, ·)` with `f(·, t)` `𝒢`-measurable, `E[A_κ f(τ) | 𝒢] = ½ ∑_t Pr_{π_k}(τ^h = t) f(t)` a.s.

**Formalization Note.** `E^{π_k}[f(τ^h)]` is the finite sum over partial trajectories with
`trajProb`. The ratio in (4) is meaningful only where `π_κ(a | s) > 0` or `π_k(a | s) = 0`; this is
the hypothesis `habs` (it holds for the positive exponential-weights policies of the paper). -/
theorem lemma_A_4 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (hP : IsTransition L P)
    (𝒢 : MeasurableSpace Ω) (h𝒢 : 𝒢 ≤ m0) (h : ℕ) (hh : h < H)
    (πk πκ : Ω → St → A → ℝ)
    (hπk : ∀ s a, Measurable[𝒢] (fun ω => πk ω s a))
    (hπκ : ∀ s a, Measurable[𝒢] (fun ω => πκ ω s a))
    (hpk : ∀ ω, IsPolicy (πk ω)) (hpκ : ∀ ω, IsPolicy (πκ ω))
    (habs : ∀ ω s a, πκ ω s a = 0 → πk ω s a = 0)
    (τ : Ω → Fin (h + 1) → St × A) (hτ : ∀ t, MeasurableSet {ω | τ ω = t})
    (hlaw : ∀ t, μ[{ω | τ ω = t}.indicator (fun _ => (1 : ℝ)) | 𝒢] =ᵐ[μ]
      fun ω => trajProb L P (πκ ω) t)
    (Acc : Ω → ℝ) (hAcc01 : ∀ ω, Acc ω = 0 ∨ Acc ω = 1) (hAccm : Measurable Acc)
    (hα : ∀ ω, 0 ≤ accProb (πk ω) (πκ ω) (τ ω) ∧ accProb (πk ω) (πκ ω) (τ ω) ≤ 1)
    (hAcc : μ[Acc | 𝒢 ⊔ MeasurableSpace.comap τ (⊤ : MeasurableSpace (Fin (h + 1) → St × A))]
      =ᵐ[μ] fun ω => accProb (πk ω) (πκ ω) (τ ω))
    (f : Ω → (Fin (h + 1) → St × A) → ℝ) (hf : ∀ t, Measurable[𝒢] (fun ω => f ω t))
    (hfb : ∃ B : ℝ, ∀ ω t, |f ω t| ≤ B) :
    μ[fun ω => Acc ω * f ω (τ ω) | 𝒢] =ᵐ[μ]
      fun ω => (1 / 2) * ∑ t, trajProb L P (πk ω) t * f ω t := by sorry

end IntroDelayAMDP
