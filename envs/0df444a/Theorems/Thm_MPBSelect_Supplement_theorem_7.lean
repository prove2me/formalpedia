-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_7
-- name    : MPBSelect.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:50:49.215484+00:00
-- url     : https://prove2.me/theorems/5b7eede0-7d11-4cd4-811e-9f398ff34e38
-- title:
--   Theorem 7 (corrected: unbounded counts) — Algorithms 3 and 4 converge to their balance systems
-- statement:
--   For either Algorithm 3 (accuracy weights) or Algorithm 4 (false-negative weights), a complete stochastic run has the following properties almost surely: the full global-balance residual tends to zero at every parameter; every ratio of the corresponding weighted empirical rates on $\Xi\cup\Xi^{\mathrm{adv}}$ tends to one; and every solution-parameter count is unbounded.
--
--   The statement is uniform in the two algorithm modes and therefore includes every conclusion for both algorithms.
--
--   Differences from the source:
--   - correction: “$\limsup_{n\to\infty}N_i^n(\theta_b)\to\infty$” → every count sequence is unbounded (equivalently $\limsup_{n\to\infty}N_i^n(\theta_b)=\infty$); reason: the printed expression is ill-typed because a limit superior is a value, not a sequence that can tend to infinity, and the same paper uses the equality form in Theorem 5
--   - encoding: Algorithms 3 and 4 are described as modifications of Algorithm 1 → a mode-indexed filtered run relation replaces exactly the weight family and the global-balance sum specified below (30); reason: universal quantification over the two modes states both printed algorithms
--   - encoding: $G_{i,n}(\theta_b)$, the plug-in $G$ with the sample ratios $\alpha_{\cdot,n}$, the posterior means and $i^b_n$ → `empiricalTrueG`, the same formula with the counts $N^n_\cdot(\theta_b)$ in place of $\alpha_{\cdot,n}(\theta_b)$ and the true $i^b$; reason: counts are $n$ times the ratios, so every ratio of two such rates is unchanged, and almost surely $i^b_n=i^b$ eventually because every count diverges (a conclusion of the theorem), so the limits coincide
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 7, p.27, with Algorithms 3-4 specified below (30), p.26; corrected using Theorem 5, p.24

import Mathlib
import Definitions.Def_MPBSelect_Supplement_Sequential

open Filter MeasureTheory
open scoped Topology

namespace MPBSelect.Supplement

/-- **Theorem 7 (strong consistency of Algorithms 3 and 4).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 7,
p.27. `mode = acc` is Algorithm 3 and `mode = fn` is Algorithm 4.

Almost surely, the allocations converge to the full global balance and the corresponding
weighted pairwise balance on `Ξ ∪ Ξ^adv`, and every pair is sampled unboundedly often.

**Formalization Note** The printed `lim sup N_i^n(θ_b) → ∞` is ill-typed; `UnboundedSampling`
states its evident intended meaning, `limsup N_i^n(θ_b)=∞`. -/
theorem theorem_7 {k B : ℕ} (mode : FavorableMode)
    (P : MPBSelect.Problem k B) (D : SequentialData P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (istar : ℕ → Ω → Fin k) (selected decision : ℕ → Ω → Fin k × Fin B)
    (hRun : IsFavorableAlgorithmRun mode P D μ F Y N istar selected decision) :
    ∀ᵐ ω ∂μ,
      (∀ b : Fin B,
        Tendsto (fun t =>
          (allocationFraction D N t ω (P.ib b) b / P.lam (P.ib b) b) ^ 2 -
            ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ P.ib b),
              (allocationFraction D N t ω j b / P.lam j b) ^ 2)
          atTop (𝓝 0)) ∧
      (∀ x ∈ favorablePairs P, ∀ x' ∈ favorablePairs P,
        Tendsto (fun t =>
          (favorableWeight mode P x.1 x.2 *
              empiricalTrueG P D Y N t ω x.1 x.2) /
            (favorableWeight mode P x'.1 x'.2 *
              empiricalTrueG P D Y N t ω x'.1 x'.2))
          atTop (𝓝 1)) ∧
      ∀ i b, UnboundedSampling N ω i b := by sorry

end MPBSelect.Supplement
