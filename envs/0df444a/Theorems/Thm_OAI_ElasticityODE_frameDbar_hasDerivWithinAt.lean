-- Prove2me | Theorems.Thm_OAI_ElasticityODE_frameDbar_hasDerivWithinAt
-- name    : OAI.ElasticityODE.frameDbar_hasDerivWithinAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:39:59.058682+00:00
-- url     : https://prove2.me/theorems/062568bc-7aa9-4dc2-9712-6fa487849754
-- title:
--   OAI.ElasticityODE.frameDbar_hasDerivWithinAt: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityODE.frameDbar_hasDerivWithinAt` of [lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityODE`, with `open Set`):
--
--   ```lean
--   lemma frameDbar_hasDerivWithinAt (b : ℂ → C(Time,R))
--       (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p : ℂ) (t : Time) :
--       HasDerivWithinAt (extend (frameDbar b p))
--         (b p t*frameDbar b p t+coefficientDbar b p t*fundamental (b p) t) Time t
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityODE.Time`, `OAI.ElasticityODE.coefficientDbar` and `OAI.ElasticityODE.extend` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityODE.frameDbar` and `OAI.ElasticityODE.fundamental` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityODE.fundamental_transport` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean (declaration OAI.ElasticityODE.frameDbar_hasDerivWithinAt)

import Mathlib
import Definitions.Def_OAIQ6El005

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
lemma frameDbar_hasDerivWithinAt (b : ℂ → C(Time,R))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p : ℂ) (t : Time) :
    HasDerivWithinAt (extend (frameDbar b p))
      (b p t*frameDbar b p t+coefficientDbar b p t*fundamental (b p) t) Time t := by
  sorry
end ElasticityODE

end
end

end OAI
end
