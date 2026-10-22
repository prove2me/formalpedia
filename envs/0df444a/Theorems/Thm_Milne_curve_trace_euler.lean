-- Prove2me | Theorems.Thm_Milne_curve_trace_euler
-- name    : Milne.curve_trace_euler
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T03:12:11.030314+00:00
-- url     : https://prove2.me/theorems/55412e74-8246-4b35-b602-3411dc49c74a
-- title:
--   The trace of the identity on the motive of a curve is its Euler characteristic
-- statement:
--   For a curve of genus g, the three Künneth idempotents decompose the motive, the trace is additive over the decomposition, and the pieces carry the signed Betti numbers 1, −2g, 1; the trace of the identity endomorphism of the motive of the curve is therefore 2 − 2g, the Euler-Poincaré characteristic (Section 6, page 10 of the source: Tr(id | hX) = Σ (−1)ⁱ bᵢ).
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 6 (p. 10): Tr(id|hX) = Σ(−1)ⁱbᵢ; for a curve of genus g, 2 − 2g.

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

universe u v

namespace Milne

/-- The trace of the identity on the motive of a curve is the
Euler-Poincaré characteristic (section 6 of the paper, page 10): for a
curve of genus g, the Künneth idempotents of the curve decompose the
motive, the trace is additive over the decomposition, and the pieces carry
the signed Betti numbers 1, −2g, 1, so the trace of the identity of
the motive of the curve is 2 − 2g. -/
theorem curve_trace_euler (W : CorrWorld.{u, v}) (g : ℕ) :
    W.trId (W.curve g) (W.delta (W.curve g)) = (2 : ℚ) - 2 * (g : ℚ) := by
  sorry

end Milne
