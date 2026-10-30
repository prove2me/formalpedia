-- Prove2me | Theorems.Thm_OAI_Tachikawa_SourceField_sourceCone_closed_boundary
-- name    : OAI.Tachikawa.SourceField.sourceCone_closed_boundary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:55:10.670791+00:00
-- url     : https://prove2.me/theorems/3adcc504-7d3a-47a2-b0b0-61e34fac692a
-- title:
--   OAI.Tachikawa.SourceField.sourceCone_closed_boundary: intermediate lemma from OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Tachikawa.SourceField.sourceCone_closed_boundary` of [lean/OAI/RingTheory/Tachikawa/Counterexample.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Counterexample.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Tachikawa.SourceField`, with `open CategoryTheory Construction`, `open scoped ModuleCat.Algebra`):
--
--   ```lean
--   lemma sourceCone_closed_boundary (a : ℤ) (ha : 0<a ∨ a≤ -2)
--       (f : DownHom.Cochain sourceCone sourceCone a) (hf : DownHom.Closed f) : DownHom.Boundary f
--   ```
--
--   **Definitions.** The statement is written with `OAI.Tachikawa.DualBimodule`, `OAI.Tachikawa.DualBimodule.instAddCommGroup`, `OAI.Tachikawa.DualBimodule.instIsScalarTower`, `OAI.Tachikawa.DualBimodule.instModule`, `OAI.Tachikawa.DualBimodule.leftModule`, `OAI.Tachikawa.DualBimodule.rightModule` and `OAI.Tachikawa.Enveloping.Alg` (definitions bundle `OAIQ116Ta000` of this split); `OAI.Tachikawa.C`, `OAI.Tachikawa.C.instAlgebra`, `OAI.Tachikawa.C.instRing` and `OAI.Tachikawa.FiniteModule` (definitions bundle `OAIQ116Ta001` of this split); `OAI.Tachikawa.DownHom.Closed`, `OAI.Tachikawa.DownHom.Cochain`, `OAI.Tachikawa.SourceField.Base`, `OAI.Tachikawa.SourceField.K` and `OAI.Tachikawa.SourceField.q` (definitions bundle `OAIQ116Ta002` of this split); `OAI.Tachikawa.Construction.E`, `OAI.Tachikawa.Construction.T`, `OAI.Tachikawa.DualBimodule.instIsScalarTowerMulOpposite` and `OAI.Tachikawa.DualBimodule.instSMulCommClassMulOpposite` (definitions bundle `OAIQ116Ta003` of this split); `OAI.Tachikawa.DownHom.Boundary` (definitions bundle `OAIQ116Ta005` of this split); `OAI.Tachikawa.Triangular.Alg`, `OAI.Tachikawa.Triangular.Off`, `OAI.Tachikawa.Triangular.instAddCommGroupOff`, `OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff`, `OAI.Tachikawa.Triangular.instModuleProdOff` and `OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff` (definitions bundle `OAIQ116Ta006` of this split); `OAI.Tachikawa.SourceField.sourceCone` and `OAI.Tachikawa.SourceField.sourceF` (definitions bundle `OAIQ116Ta016` of this split).
--
--   **Used by.** The proof of `OAI.Tachikawa.main_theorem` of this split imports it.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Counterexample.lean (declaration OAI.Tachikawa.SourceField.sourceCone_closed_boundary)

import Mathlib
import Definitions.Def_OAIQ116Ta016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Tachikawa.SourceField
open CategoryTheory Construction
open scoped ModuleCat.Algebra

local instance sourceF_left_r2247d4_1 : Module.Projective (E q) (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).1
local instance sourceF_right_r2247d4_1 : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).2
local instance sourceF_finite_r2247d4_1 : FiniteDimensional K (Enveloping.Obj sourceF.obj) :=
  inferInstanceAs (FiniteDimensional K sourceF)
lemma sourceCone_closed_boundary (a : ℤ) (ha : 0<a ∨ a≤ -2)
    (f : DownHom.Cochain sourceCone sourceCone a) (hf : DownHom.Closed f) : DownHom.Boundary f := by
  sorry

end Tachikawa.SourceField

end

end OAI
end
