-- Prove2me | Theorems.Thm_OAI_CriticalStrip_Diagram_nextScalar_homogeneous_of_ne
-- name    : OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T01:47:29.977421+00:00
-- url     : https://prove2.me/theorems/08748696-8b3b-42ae-8415-41aafbd25897
-- title:
--   OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne: intermediate lemma from OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne` of [lean/OAI/Combinatorics/StripMass/StripMass/MonicPositive.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/MonicPositive.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalStrip.Diagram`, with `open Filter Polynomial`, `open scoped Topology BigOperators Classical`):
--
--   ```lean
--   lemma nextScalar_homogeneous_of_ne {n : ℕ} (hn : 1≤n)
--       (hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0) :
--       ∃ g : Polynomial ℝ, MonicProblem n g ∧
--         nextScalar (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=
--           Polynomial.C (scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))) * g.map Complex.ofRealHom
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalStrip.Diagram.C` (definitions bundle `OAIQ042S000` of this split); `OAI.CriticalStrip.MonicProblem` (definitions bundle `OAIQ042S001` of this split); `OAI.CriticalStrip.Diagram.scalarValue` (definitions bundle `OAIQ042S007` of this split); `OAI.CriticalStrip.Diagram.nextScalar` (definitions bundle `OAIQ042S008` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalStrip.Diagram.deformationAngles_scalar_ne_zero`, `OAI.CriticalStrip.Diagram.scalarValue_homogeneous_ne_zero` and `OAI.CriticalStrip.critical_strip_mass` of this split import it.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/MonicPositive.lean (declaration OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne)

import Mathlib
import Definitions.Def_OAIQ042S007
import Definitions.Def_OAIQ042S008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CriticalStrip.Diagram
noncomputable section
open Filter Polynomial
open scoped Topology BigOperators Classical

lemma nextScalar_homogeneous_of_ne {n : ℕ} (hn : 1≤n)
    (hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      nextScalar (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=
        Polynomial.C (scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))) * g.map Complex.ofRealHom := by
  sorry

end
end CriticalStrip.Diagram

end OAI
end
