-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_subseq_integral_bounds_of_convex_epigraph_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:22.047835+00:00
-- url     : https://prove2.me/theorems/475ba44f-a554-43ce-bfd2-ddb53b1e5734
-- title:
--   Full Integral And Conjugate-Mass Compactness Bounds
-- statement:
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $dx$ be an additive Haar measure, let $\mu$ be a finite measure, and assume $0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Let $\phi_j:E\to\overline{\mathbb R}$ satisfy:
--
--   1. $\phi_j\ge0$ and $\phi_j(0)=0$.
--   2. Every real epigraph of $\phi_j$ is convex.
--   3. Each $\phi_j.\operatorname{toENNReal}$ is a.e. measurable with respect to $\mu$.
--   4. $\sup_j\int^-\phi_j.\operatorname{toENNReal}\,d\mu\ne+\infty$.
--
--   Then there exist a strictly increasing $s:\mathbb N\to\mathbb N$ and $\psi:E\to\overline{\mathbb R}$ such that $\psi\ge0$, $\psi(0)=0$, its real epigraph is convex, and $\psi.\operatorname{toENNReal}$ is measurable. On the interior of the support convex hull, $\psi$ is finite and
--   $$\phi_{s(j)}(x)\longrightarrow\psi(x).$$
--   The function $\psi$ is radially closed and equals $+\infty$ outside the closure of that interior. In addition, `PotentialIntegrable ψ μ` holds,
--   $$\operatorname{mass}(dx,\psi^*)\ne+\infty,$$
--   $$\int^-\psi.\operatorname{toENNReal}\,d\mu\le\liminf_{j\to\infty}\int^-\phi_{s(j)}.\operatorname{toENNReal}\,d\mu,$$
--   and
--   $$\limsup_{j\to\infty}\operatorname{mass}(dx,\phi_{s(j)}^*)\le\operatorname{mass}(dx,\psi^*).$$
--
--   This declaration combines the pointwise compactness, integral lower semicontinuity, and conjugate-mass upper semicontinuity conclusions; it does not assert variational attainment.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_subseq_integral_bounds_of_convex_epigraph
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
--       [MeasurableSpace E] [BorelSpace E]
--       (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
--       (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
--       (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
--       (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
--       (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
--       (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
--       ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
--         Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
--         Measurable (fun x => (ψ x).toENNReal) ∧
--         (∀ x ∈ interior (convexHull ℝ μ.support),
--           ψ x ≠ ⊤ ∧ Tendsto (fun j => φ (s j) x) atTop (𝓝 (ψ x))) ∧
--         (∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x))) ∧
--         (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
--         PotentialIntegrable ψ μ ∧ mass dx (legendre ψ) ≠ ⊤ ∧
--         (∫⁻ x, (ψ x).toENNReal ∂μ ≤
--           liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) atTop) ∧
--         limsup (fun j => mass dx (legendre (φ (s j)))) atTop ≤ mass dx (legendre ψ)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Compactness`](https://prove2.me/theorems/cbdff6c6-a5ae-41ee-946b-9f0ca1da6699).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`limsup_mass_legendre_le`](https://prove2.me/theorems/a6e9fd8e-5a77-41be-9761-9a4957084c5b), [`exists_subseq_lintegral_le_liminf_of_convex_epigraph`](https://prove2.me/theorems/27a45796-950c-4905-a61b-2943ad71aab6).
--
--   Previous: [`exists_subseq_lintegral_le_liminf_of_convex_epigraph`](https://prove2.me/theorems/27a45796-950c-4905-a61b-2943ad71aab6).
--
--   [Source excerpt, lines 244–263](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean#L244-L263) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma 17, (56), of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Compactness of normalised potentials.”
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean#L239-L284 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Compactness`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Compactness

open MeasureTheory
open Filter
open scoped Topology
open FunctionalInequalities.Analysis

theorem FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ interior (convexHull ℝ μ.support),
        ψ x ≠ ⊤ ∧ Tendsto (fun j => φ (s j) x) atTop (𝓝 (ψ x))) ∧
      (∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x))) ∧
      (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
      PotentialIntegrable ψ μ ∧ mass dx (legendre ψ) ≠ ⊤ ∧
      (∫⁻ x, (ψ x).toENNReal ∂μ ≤
        liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) atTop) ∧
      limsup (fun j => mass dx (legendre (φ (s j)))) atTop ≤ mass dx (legendre ψ) := by sorry
