-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_explicit_bound
-- name    : ListReplicableBias.LowerBound.explicit_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:07.084455+00:00
-- url     : https://prove2.me/theorems/97b7ae00-9e44-4977-be66-437af72c8e01
-- title:
--   §5.4 display — The exact 3/12800 sample lower bound
-- statement:
--   Let $0<\varepsilon,\delta<1/8$ and suppose $d\in\mathbb N$ satisfies $20\ln(2(d+1))\le d$. Every $(d+1,\varepsilon,\delta)$-list replicable randomized adaptive algorithm drawing $N$ samples satisfies
--   $$N\ge\frac{3}{12800}\,\frac{d^2}{\varepsilon^2\ln(2(d+1))}.$$
--   The constant is the source's exact value; Appendix B repeats it for arbitrary algorithms (PDF p. 15). The threshold is the precise admissibility condition on the radius selected in the paper.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - encoding: arbitrary randomized adaptive sampling algorithms and full histories → an arbitrary probability seed space, prefix-dependent coin choices, and the explicit transcript density; failure is `none`; reason: all private randomness is included in the seed, earlier choices are recoverable from it and earlier outcomes, and ignored tosses pad a fixed cap without changing the output law
--   - encoding: sufficiently large d so that the selected radius is at most 2 epsilon → the explicit condition 20 ln(2(d+1)) ≤ d, with Real.log; reason: for positive epsilon and d this is exactly the radius condition; d=0 fails this inequality
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, §5.4 display, PDF p. 7 (arbitrary-transcript extension: Appendix B, PDF p. 15)

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- §5.4 final display, PDF p. 7, repeated in Appendix B, PDF p. 15.
The threshold is exactly the condition for the paper's chosen radius to be admissible. -/
theorem explicit_bound {d N : ℕ} (A : SamplingAlgorithm d N) (ε δ : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 8)) (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 8))
    (hd : 20 * Real.log (2 * ((d : ℝ) + 1)) ≤ (d : ℝ))
    (hA : IsListReplicable A (d + 1) ε δ) :
    (3 / 12800 : ℝ) * (d : ℝ) ^ 2 /
      (ε ^ 2 * Real.log (2 * ((d : ℝ) + 1))) ≤ (N : ℝ) := by sorry

end ListReplicableBias.LowerBound
