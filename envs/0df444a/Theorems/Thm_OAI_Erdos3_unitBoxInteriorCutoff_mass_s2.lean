-- Prove2me | Theorems.Thm_OAI_Erdos3_unitBoxInteriorCutoff_mass_s2
-- name    : OAI.Erdos3.unitBoxInteriorCutoff_mass_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:10.810362+00:00
-- url     : https://prove2.me/theorems/170f48af-1442-41fc-a4ab-d3fadf4218b0
-- title:
--   The smooth interior cutoff of the unit cube at margin r has integral at least 1 - 4·dim·r
-- statement:
--   Let $\iota$ be a finite type and $r > 0$ a real number. Let `unitBoxInteriorCutoff r` be OpenAI's function on $\mathbb{R}^\iota$ given by
--   $$x \mapsto \prod_{i \in \iota} \sigma\bigl(x_i / r - 1\bigr)\, \sigma\bigl((1 - x_i)/r - 1\bigr),$$
--   the product over all faces (pairs in $\operatorname{Bool} \times \iota$) of Mathlib's `Real.smoothTransition` $\sigma$ applied to (distance to the face)$/r - 1$ (OpenAI's `inequalityBoundaryCutoff` with the face functions `unitBoxFace`). Then
--   $$1 - 4 \cdot \#\iota \cdot r \le \int_{\mathbb{R}^\iota} \texttt{unitBoxInteriorCutoff}\ r\ (x)\, dx,$$
--   the integral being with respect to Lebesgue measure.
--
--   Lean: `OAI.Erdos3.unitBoxInteriorCutoff_mass_s2`, which states OpenAI's `OAI.Erdos3.unitBoxInteriorCutoff_mass` (in `lean/OAI/Combinatorics/Progressions/Geometry/UnitBoxInteriorCutoff.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B067` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/UnitBoxInteriorCutoff.lean (declaration OAI.Erdos3.unitBoxInteriorCutoff_mass)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B067

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {ι : Type*} [Fintype ι]

theorem unitBoxInteriorCutoff_mass_s2 {r : ℝ} (hr : 0 < r) :
    1 - 4 * Fintype.card ι * r ≤ ∫ x : ι → ℝ, unitBoxInteriorCutoff r x := by
  sorry

end Erdos3

end

end OAI
end
