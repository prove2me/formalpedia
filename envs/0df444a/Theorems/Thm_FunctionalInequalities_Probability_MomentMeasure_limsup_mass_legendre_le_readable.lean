-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_limsup_mass_legendre_le_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:16.956985+00:00
-- url     : https://prove2.me/theorems/a6e9fd8e-5a77-41be-9761-9a4957084c5b
-- title:
--   Upper Semicontinuity Of Legendre Conjugate Mass
-- statement:
--   Let $E$ be finite-dimensional with an additive Haar measure $dx$. Let $\phi_j,\psi:E\to\overline{\mathbb R}$ and let $K\subseteq E$ be open and convex with $0\in K$. Assume:
--
--   1. $\psi$ is finite-valued in the extended-real sense on $K$.
--   2. $\phi_j(x)\to\psi(x)$ for every $x\in K$.
--   3. $\psi(tx)\to\psi(x)$ as $t\to1$ from below for every $x$.
--   4. $\psi(x)=+\infty$ whenever $x\notin\overline K$.
--
--   Then
--   $$\operatorname{mass}(dx,\psi^*)\ne+\infty$$
--   and
--   $$\limsup_{j\to\infty}\operatorname{mass}(dx,\phi_j^*)\le\operatorname{mass}(dx,\psi^*).$$
--
--   No finiteness of the individual source masses is assumed, and the conclusion permits zero mass.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem limsup_mass_legendre_le
--       (dx : Measure E) [dx.IsAddHaarMeasure]
--       (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
--       (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
--       (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
--       (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
--       (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
--       (hoff : ∀ x ∉ closure K, ψ x = ⊤) :
--       mass dx (legendre ψ) ≠ ⊤ ∧
--         limsup (fun j => mass dx (legendre (φ j))) atTop ≤ mass dx (legendre ψ)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`legendre_eq_interior_sup`](https://prove2.me/theorems/fb27a67d-8a39-4dbc-904c-e8977c7bb3af), [`exists_integrable_exponential_domination`](https://prove2.me/theorems/0002089c-2c4b-4c6b-8010-16b85c45339e), [`limsup_density_legendre_le`](https://prove2.me/theorems/50c36fd7-1bb7-40be-8a5b-91f04f40fa30).
--
--   Previous: [`exists_integrable_exponential_domination`](https://prove2.me/theorems/0002089c-2c4b-4c6b-8010-16b85c45339e) · Next: [`log_sub_ge_of_integral_limits`](https://prove2.me/theorems/8c2c9203-7701-486b-b236-68a42ba9b8b5).
--
--   [Source excerpt, lines 156–165](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L156-L165) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Compactness of normalised potentials,” in a partial form.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L153-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open FunctionalInequalities.Analysis
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le_readable
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) :
    mass dx (legendre ψ) ≠ ⊤ ∧
      limsup (fun j => mass dx (legendre (φ j))) atTop ≤ mass dx (legendre ψ) := by sorry
