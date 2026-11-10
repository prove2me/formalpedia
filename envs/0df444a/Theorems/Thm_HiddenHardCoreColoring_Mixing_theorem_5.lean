-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_theorem_5
-- name    : HiddenHardCoreColoring.Mixing.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:19.519812+00:00
-- url     : https://prove2.me/theorems/7a19af7f-1cf7-431e-9b3b-39a21a57b362
-- title:
--   Theorem 5 ([CFYZ24]) — uniform hard-core gap below (1 − δ)λ_crit(Δ) for all Δ ≥ 3
-- statement:
--   For every $\delta\in(0,1)$ there is $\theta^*(\delta)\in(0,1]$ such that for every $\Delta\ge3$, every graph on $n\ge1$ vertices of maximum degree at most $\Delta$, and all vertex activities with $0<\lambda_v\le(1-\delta)\lambda_{\mathrm{crit}}(\Delta)$, where $\lambda_{\mathrm{crit}}(\Delta)=(\Delta-1)^{\Delta-1}/(\Delta-2)^\Delta$, the Glauber dynamics $P^\nu$ of the hard-core model satisfies
--   $$\operatorname{gap}(P^\nu)\ge\frac{\theta^*(\delta)}n,\qquad\text{hence}\qquad\operatorname{gap}(H)=n\operatorname{gap}(P^\nu)\ge\theta^*(\delta).$$
--   The constant depends only on $\delta$: not on $\Delta$, $n$, the graph or the activities.
--
--   The paper cites this result of Chen, Feng, Yin and Zhang (its footnote on p.8 notes that the vertex-dependent, degree-at-most-$\Delta$ form follows from their argument); its uniformity in $\Delta$ is what makes the hidden hard-core gaps of Corollary 17 uniform.
--
--   Differences from the source:
--   - encoding: there is a function θ*(δ) ∈ (0,1] → for each δ ∈ (0,1) there is θ ∈ (0,1]; reason: equivalent by choice; θ is chosen before Δ, the graph and the activities
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Theorem 5 and footnote 1, p.8

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Theorem 5** ([CFYZ24]; Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.8). For every `δ ∈ (0, 1)` there is `θ*(δ) ∈ (0, 1]` such
that, for every `Δ ≥ 3`, every `n`-vertex graph of maximum degree at most `Δ`, and all activities
`0 < λ_v ≤ (1 − δ)λ_crit(Δ)`, `gap(P^ν) ≥ θ*(δ)/n`, and hence `gap(H) ≥ θ*(δ)`. -/
theorem theorem_5 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∀ Δ : ℕ, 3 ≤ Δ →
        ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (H : SimpleGraph W)
          [DecidableRel H.Adj], (∀ w, H.degree w ≤ Δ) →
          ∀ lam : W → ℝ, (∀ w, 0 < lam w ∧ lam w ≤ (1 - δ) * lamCrit Δ) →
            θ / (Fintype.card W : ℝ) ≤ gap (hcP H lam) ∧ θ ≤ hcGapH H lam := by sorry

end HiddenHardCoreColoring.Mixing
