-- Prove2me | Theorems.Thm_OAI_PiExponentSeshadri_Geometry_isAffineOpen_of_fullSupport_preimage_q68
-- name    : OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:14:15.168558+00:00
-- url     : https://prove2.me/theorems/e9dd4c26-abfa-4c55-ba38-0700fab74952
-- title:
--   OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage` of [lean/OAI/NumberTheory/PiExponent/Ampleness/NilpotentAmpleDescent.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/NilpotentAmpleDescent.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`):
--
--   ```lean
--   theorem isAffineOpen_of_fullSupport_preimage_q68 [IsNoetherian X]
--       (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.Opens)
--       (hU : IsAffineOpen (I.subschemeι ⁻¹ᵁ U)) : IsAffineOpen U
--   ```
--
--   **Used by.** The proof of `OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/NilpotentAmpleDescent.lean (declaration OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {X : Scheme.{0}}

theorem isAffineOpen_of_fullSupport_preimage_q68 [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.Opens)
    (hU : IsAffineOpen (I.subschemeι ⁻¹ᵁ U)) : IsAffineOpen U := by
  sorry

end
end PiExponentSeshadri.Geometry

end OAI
end
