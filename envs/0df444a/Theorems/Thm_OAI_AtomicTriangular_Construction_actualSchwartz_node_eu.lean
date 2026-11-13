-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_node_eu
-- name    : OAI.AtomicTriangular.Construction.actualSchwartz_node_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:57:04.383201+00:00
-- url     : https://prove2.me/theorems/25e3f66a-c2c0-49c6-bc79-8315086bffb1
-- title:
--   OAI.AtomicTriangular.Construction.actualSchwartz_node_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualSchwartz_node` of [lean/OAI/Analysis/Triangular/Construction/Normalization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators FourierTransform SchwartzMap`, `open Complex`):
--
--   ```lean
--   lemma actualSchwartz_node_eu {α : ℝ} (hα : 1 ≤ α) (x : Plane) (n : Node) (hx : radial x=n.val) :
--       actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x = AtomicTriangular.gaussian α x ∧
--         actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.Node` and `OAI.AtomicTriangular.Construction.residues` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.Plane`, `OAI.AtomicTriangular.Construction.Z` and `OAI.AtomicTriangular.Construction.actualSchwartz` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.Construction.radial` (definitions bundle `OAIQ334E007` of this split); `OAI.AtomicTriangular.gaussian` (definitions bundle `OAIQ334E008` of this split); `OAI.AtomicTriangular.Construction.gaussianZ` and `OAI.AtomicTriangular.Construction.gaussianZ_bounds` (definitions bundle `OAIQ334E009` of this split).
--
--   **Used by.** The definitions bundle `OAIQ334E033` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean (declaration OAI.AtomicTriangular.Construction.actualSchwartz_node)

import Mathlib
import Definitions.Def_OAIQ334E009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_node_eu {α : ℝ} (hα : 1 ≤ α) (x : Plane) (n : Node) (hx : radial x=n.val) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x = AtomicTriangular.gaussian α x ∧
      actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x=0 := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
