-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_integrable_exponential_domination_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:58.705575+00:00
-- url     : https://prove2.me/theorems/0002089c-2c4b-4c6b-8010-16b85c45339e
-- title:
--   Common Exponential Domination Of Conjugate Densities
-- statement:
--   This is the common-dominator construction used for the upper semicontinuity result associated with Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as a partial formalization.
--
--   Let $E$ be finite-dimensional with an additive Haar measure $dx$. Let $\phi_j:E\to\overline{\mathbb R}$, $\psi:E\to\overline{\mathbb R}$, and let $K\subseteq E$ be open with $0\in K$. Assume:
--
--   1. For every $x\in K$, $\psi(x)$ is neither $+\infty$ nor $-\infty$.
--   2. For every $x\in K$, $\phi_j(x)\to\psi(x)$ as $j\to\infty$.
--
--   Then there exist $c,M\in\mathbb R$ and $N\in\mathbb N$ with $c>0$ such that
--   $$\int_E\operatorname{ENNReal.ofReal}\!\left(\exp(M-c\|y\|)\right)\,dx(y)\ne+\infty,$$
--   while, for every $y\in E$,
--   $$\operatorname{density}(\psi^*)(y)\le\operatorname{ENNReal.ofReal}\!\left(\exp(M-c\|y\|)\right),$$
--   and for every $j\ge N$ the same bound holds with $\psi$ replaced by $\phi_j$.
--
--   This supplies a single integrable exponential envelope for the limiting and eventually indexed conjugate densities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_integrable_exponential_domination
--       (dx : Measure E) [dx.IsAddHaarMeasure]
--       (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
--       (hK : IsOpen K) (h0 : (0 : E) ∈ K)
--       (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
--       (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x))) :
--       ∃ (c M : ℝ) (N : ℕ), 0 < c ∧
--         (∫⁻ y, ENNReal.ofReal (Real.exp (M - c * ‖y‖)) ∂dx) ≠ ⊤ ∧
--         (∀ y, density (legendre ψ) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖))) ∧
--         ∀ j, N ≤ j → ∀ y,
--           density (legendre (φ j)) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`affineMaximum_coercive`](https://prove2.me/theorems/e32066d6-367b-466d-9089-f5d72ac05f70), [`eventually_affineMaximum_sub_le_legendre`](https://prove2.me/theorems/5b6258b4-53ab-4ec0-9b82-126b22c2ab6c), [`integrable_exp_sub_norm`](https://prove2.me/theorems/6e84bf56-c441-4d85-881f-7cdd5b15ecb5).
--
--   Previous: [`limsup_density_legendre_le`](https://prove2.me/theorems/50c36fd7-1bb7-40be-8a5b-91f04f40fa30) · Next: [`limsup_mass_legendre_le`](https://prove2.me/theorems/a6e9fd8e-5a77-41be-9761-9a4957084c5b).
--
--   [Source excerpt, lines 118–128](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L118-L128) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L115-L151 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open FunctionalInequalities.Analysis
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination_readable
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x))) :
    ∃ (c M : ℝ) (N : ℕ), 0 < c ∧
      (∫⁻ y, ENNReal.ofReal (Real.exp (M - c * ‖y‖)) ∂dx) ≠ ⊤ ∧
      (∀ y, density (legendre ψ) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖))) ∧
      ∀ j, N ≤ j → ∀ y,
        density (legendre (φ j)) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖)) := by sorry
