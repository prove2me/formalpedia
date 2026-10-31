-- Prove2me | Theorems.Thm_FoundationsRL_DECExamples_cover_reduction
-- name    : FoundationsRL.DECExamples.cover_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:20:33.885752+00:00
-- url     : https://prove2.me/theorems/905e2b62-d4e0-438f-8577-db5b7fcc385d
-- title:
--   Proof of Proposition 18, first display — reduction to the $\varepsilon$-cover by the Lipschitz property
-- statement:
--   Let $(\Pi,\rho)$ be a metric space, $\Pi'\subseteq\Pi$ a finite $\varepsilon$-cover, $f:\Pi\to[0,1]$ a $1$-Lipschitz function and $p$ any distribution on $\Pi$. Then:
--
--   1. there is a map $\iota:\Pi\to\Pi'$ with $\rho(\pi,\iota(\pi))\le\varepsilon$ for all $\pi$;
--   2. for every such map and every point $\pi_0$ (in particular a maximizer $\pi_0=\pi_f$ of $f$),
--   $$
--   \begin{aligned}
--   \mathbb E_{\pi\sim p}[f(\pi_0)-f(\pi)]&\le\mathbb E_{\pi\sim p}[f(\iota(\pi_0))-f(\pi)]+|f(\pi_0)-f(\iota(\pi_0))|\\
--   &\le\mathbb E_{\pi\sim p}[f(\iota(\pi_0))-f(\pi)]+\rho(\pi_0,\iota(\pi_0))\\
--   &\le\mathbb E_{\pi\sim p}[f(\iota(\pi_0))-f(\pi)]+\varepsilon;
--   \end{aligned}
--   $$
--   3. without assuming a maximizer exists,
--   $$
--   \mathbb E_{\pi\sim p}\Big[\sup_{\pi'\in\Pi}f(\pi')-f(\pi)\Big]\le\mathbb E_{\pi\sim p}\Big[\max_{\pi'\in\Pi'}f(\pi')-f(\pi)\Big]+\varepsilon.
--   $$
--
--   This reduces the regret against the whole space to the regret against the finite cover, at an additive cost $\varepsilon$.
--
--   **Formalization Note** "Any distribution" is any Borel probability measure on $\Pi$, and expectations are integrals; every integrand is bounded and continuous, so integrable. The decision space is written `D` in Lean.
--
--   Differences from the source:
--   - generalization: the chain at π_f, a maximizer of f → the chain at every point π₀, plus clause 3 stated with sup_Π f; reason: π_f need not exist on a non-compact space; at π₀ = π_f clause 2 is the display, and clause 3 is its form when no maximizer exists
--   - encoding: any distribution p → any Borel probability measure μ, with expectations as Bochner integrals; reason: f is continuous and bounded, so every integrand is integrable; a PMF is the case μ = p.toMeasure
--   - generalization: Π′ the ε-cover witnessing N_ρ(Π, ε), for ε > 0 → any finite ε-cover, for any ε ≥ 0; reason: the display uses only the covering property, and a witness is a finite ε-cover
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 18, first display, p. 74

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_lipschitzClass
open scoped NNReal

namespace FoundationsRL.DECExamples

/-- **Proof of Proposition 18, first display: reduction to the cover.** If `D'` is an `ε`-cover and
`f` is `1`-Lipschitz, there is a map `ι` into `D'` with `ρ(π, ι(π)) ≤ ε`, and for any such map and
any distribution `μ`, `E_{π∼μ}[f(π_f) − f(π)] ≤ E_{π∼μ}[f(ι(π_f)) − f(π)] + |f(π_f) − f(ι(π_f))|
≤ E_{π∼μ}[f(ι(π_f)) − f(π)] + ρ(π_f, ι(π_f)) ≤ E_{π∼μ}[f(ι(π_f)) − f(π)] + ε`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 18, p. 74.

**Formalization Note.** "Any distribution" is any Borel probability measure `μ`, and expectations are
Bochner integrals. They carry no junk value: `f` is continuous and bounded, so every integrand is
integrable. A `PMF` is the case `μ = p.toMeasure`, where the integrals are the `tsum`s of `expect`.
The chain is stated at every point `π₀`, in particular at a maximizer `π_f` when one exists. The last
clause is the form that needs no maximizer: `f(π_f)` is `⨆ π, f π`, and `f(ι(π_f))` is bounded by the
maximum of `f` over the cover. -/
theorem cover_reduction {D : Type*} [MetricSpace D] [MeasurableSpace D] [BorelSpace D] (ε : ℝ≥0)
    (D' : Finset D) (hcover : Metric.IsCover ε Set.univ (D' : Set D)) (f : D → ℝ)
    (hf : f ∈ lipschitzClass D) (μ : MeasureTheory.Measure D)
    [MeasureTheory.IsProbabilityMeasure μ] :
    (∃ ι : D → D, ∀ π, ι π ∈ D' ∧ dist π (ι π) ≤ ε) ∧
    (∀ ι : D → D, (∀ π, ι π ∈ D' ∧ dist π (ι π) ≤ ε) → ∀ π₀ : D,
      ∫ π, (f π₀ - f π) ∂μ ≤ ∫ π, (f (ι π₀) - f π) ∂μ + |f π₀ - f (ι π₀)| ∧
      ∫ π, (f (ι π₀) - f π) ∂μ + |f π₀ - f (ι π₀)| ≤
          ∫ π, (f (ι π₀) - f π) ∂μ + dist π₀ (ι π₀) ∧
      ∫ π, (f (ι π₀) - f π) ∂μ + dist π₀ (ι π₀) ≤ ∫ π, (f (ι π₀) - f π) ∂μ + ε) ∧
    ∫ π, ((⨆ π', f π') - f π) ∂μ ≤ ∫ π, ((⨆ π' : D', f π') - f π) ∂μ + ε := by sorry

end FoundationsRL.DECExamples
