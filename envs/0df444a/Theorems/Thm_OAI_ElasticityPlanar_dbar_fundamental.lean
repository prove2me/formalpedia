-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_dbar_fundamental
-- name    : OAI.ElasticityPlanar.dbar_fundamental
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:40:45.659055+00:00
-- url     : https://prove2.me/theorems/64f90066-84fd-4365-877c-745761e9f1b4
-- title:
--   OAI.ElasticityPlanar.dbar_fundamental: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.dbar_fundamental` of [lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open Set Complex Module`, `open ElasticityODE ElasticityCompact`):
--
--   ```lean
--   lemma dbar_fundamental (b : ℂ → C(Time,R)) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (z : ℂ) (t : Time) :
--       classicalDbar (fun z => fundamental (b z) t) z=frameDbar b z t
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityODE.Time` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityPlanar.classicalDbar` (definitions bundle `OAIQ6El003` of this split); `OAI.ElasticityODE.frameDbar` and `OAI.ElasticityODE.fundamental` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityPlanar.spatial_frame_of_left_inverse` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean (declaration OAI.ElasticityPlanar.dbar_fundamental)

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
open Set Complex Module
namespace ElasticityPlanar
open ElasticityODE ElasticityCompact
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
lemma dbar_fundamental (b : ℂ → C(Time,R)) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (z : ℂ) (t : Time) :
    classicalDbar (fun z => fundamental (b z) t) z=frameDbar b z t := by
  sorry
end ElasticityPlanar

end
end

end OAI
end
