-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_dimension_bound
-- name    : MultipleUnicast.Counterexample.dimension_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:35.35806+00:00
-- url     : https://prove2.me/theorems/4e656e47-f0fa-473d-a5c9-ddf38874a60d
-- title:
--   Appendix B, Proposition (unnumbered) — compatible-space dimension
-- statement:
--   Let $W$ be the actual $\mathbb F_9$ subspace of assignments to the candidate incidence edges satisfying the homogeneous quartic rule at every point and the cubed-coordinate quartic rule at every line. Then
--   $$\dim_{\mathbb F_9}W\ge166.$$
--   No dimension or independence assumption is supplied. This is the supporting dimension assertion used in §4, with the same ordered field and local-coordinate conventions.
--
--   Differences from the source:
--   - encoding: local incident vectors and restriction W_C → F9^B → masked local linear maps, submodule preimages, and the literal coordinate restriction; reason: zero masking outside an incident set adds no local condition
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, Appendix B, Proposition (unnumbered), PDF p. 16 / printed p. 15; local rules on PDF pp. 15–16 / printed pp. 14–15

import Definitions.Def_MultipleUnicast_Counterexample_LocalSpace

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample

/-- Appendix B, Proposition (unnumbered), PDF 16 / printed 15. -/
theorem dimension_bound : 166 ≤ Module.finrank F9 W := by sorry

end MultipleUnicast.Counterexample
