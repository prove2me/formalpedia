-- Prove2me | Theorems.Thm_OAI_Erdos3_normalizedMesh_scale_large
-- name    : OAI.Erdos3.normalizedMesh_scale_large
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:15:59.858883+00:00
-- url     : https://prove2.me/theorems/68495d13-2637-4d6c-b592-a51c535f75f1
-- title:
--   A scale above 4·exp(inverseLog + lengthLog) makes delta·scale at least 4
-- statement:
--   Let $\delta$, $\mathrm{scale}$, $\mathrm{inverseLog}$, $\mathrm{lengthLog}$ be real numbers with $0<\delta$, $\delta^{-1}\le e^{\mathrm{inverseLog}}$, $0\le \mathrm{lengthLog}$, and $4\,e^{\mathrm{inverseLog}+\mathrm{lengthLog}}\le \mathrm{scale}$. Then $4\le \delta\cdot\mathrm{scale}$.
--
--   Lean: `OAI.Erdos3.normalizedMesh_scale_large` in `lean/OAI/Combinatorics/Progressions/Estimates/NormalizedMeshLengths.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/NormalizedMeshLengths.lean#L20

import Mathlib
import Definitions.Def_ErdosReciprocal

namespace OAI

section

namespace Erdos3

theorem normalizedMesh_scale_large {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hlength : 0 ≤ lengthLog) (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    4 ≤ delta * scale := by
  sorry

end Erdos3
end
end OAI
