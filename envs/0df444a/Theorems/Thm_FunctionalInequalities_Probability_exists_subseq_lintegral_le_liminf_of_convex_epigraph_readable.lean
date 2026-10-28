-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_subseq_lintegral_le_liminf_of_convex_epigraph_readable
-- name    : FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:14.359508+00:00
-- url     : https://prove2.me/theorems/27a45796-950c-4905-a61b-2943ad71aab6
-- title:
--   Subsequence Compactness For Extended-Real Convex Potentials
-- statement:
--   This formalizes the first half, (56a), of Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Compactness of normalised potentials.”
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $\mu$ be a finite measure such that $0$ lies in the interior of the convex hull of its support. Let $\phi_j:E\to\overline{\mathbb R}$ satisfy:
--
--   1. $\phi_j(x)\ge0$ for every $j,x$.
--   2. $\phi_j(0)=0$.
--   3. Each real epigraph of $\phi_j$ is convex.
--   4. Each $x\mapsto(\phi_j(x)).\operatorname{toENNReal}$ is a.e. measurable.
--   5. The supremum of their lower integrals is finite:
--      $$\sup_j\int^- (\phi_j(x)).\operatorname{toENNReal}\,d\mu(x)\ne+\infty.$$
--
--   Then there are a strictly increasing subsequence map $s:\mathbb N\to\mathbb N$ and $\psi:E\to\overline{\mathbb R}$ such that $\psi\ge0$, $\psi(0)=0$, its real epigraph is convex, and $\psi.\operatorname{toENNReal}$ is measurable. On the interior of the support convex hull, $\psi$ is finite and
--   $$\phi_{s(j)}(x)\longrightarrow\psi(x).$$
--   Moreover, $\psi$ is radially closed, equals $+\infty$ outside the closure of that interior, and
--   $$\int^-\psi(x).\operatorname{toENNReal}\,d\mu(x)\le\liminf_{j\to\infty}\int^- (\phi_{s(j)}(x)).\operatorname{toENNReal}\,d\mu(x).$$
--
--   This is the compactness and lower-integral part of the convex-potential argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_subseq_lintegral_le_liminf_of_convex_epigraph {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (μ : Measure E) [IsFiniteMeasure μ] (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
--       (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
--       (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
--       (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
--       (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
--       ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
--         Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
--         Measurable (fun x => (ψ x).toENNReal) ∧
--         (∀ x ∈ interior (convexHull ℝ μ.support),
--           ψ x ≠ ⊤ ∧ Filter.Tendsto (fun j => φ (s j) x) Filter.atTop (nhds (ψ x))) ∧
--         (∀ x, Filter.Tendsto (fun t : ℝ => ψ (t • x)) (nhdsWithin 1 (Set.Iio 1)) (nhds (ψ x))) ∧
--         (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
--         ∫⁻ x, (ψ x).toENNReal ∂μ ≤
--           Filter.liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) Filter.atTop
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Compactness`](https://prove2.me/theorems/cbdff6c6-a5ae-41ee-946b-9f0ca1da6699).
--
--   Supporting theorems: [`exists_subseq_tendsto_of_convexOn_of_bddAbove`](https://prove2.me/theorems/1673fa59-924b-4b3b-a359-a75c6d0c9acb), [`exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`](https://prove2.me/theorems/47effa70-14be-45e1-bd3e-85ca90620000), [`real_convexOn_effective_domain`](https://prove2.me/theorems/f7c7760e-e128-40c5-a6ce-efaac3655fcc), [`radialExtension_radial_limit`](https://prove2.me/theorems/bbb9246f-b710-4e74-a805-3997176540ae).
--
--   Next: [`exists_subseq_integral_bounds_of_convex_epigraph`](https://prove2.me/theorems/475ba44f-a554-43ce-bfd2-ddb53b1e5734).
--
--   [Source excerpt, lines 109–124](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean#L109-L124) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean#L105-L227 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Compactness`, declaration `FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Compactness

open MeasureTheory

theorem FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ interior (convexHull ℝ μ.support),
        ψ x ≠ ⊤ ∧ Filter.Tendsto (fun j => φ (s j) x) Filter.atTop (nhds (ψ x))) ∧
      (∀ x, Filter.Tendsto (fun t : ℝ => ψ (t • x)) (nhdsWithin 1 (Set.Iio 1)) (nhds (ψ x))) ∧
      (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
      ∫⁻ x, (ψ x).toENNReal ∂μ ≤
        Filter.liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) Filter.atTop := by sorry
