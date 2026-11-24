-- Prove2me | Theorems.Thm_GlobalTheory_HCA_mem_solG
-- name    : GlobalTheory.HCA.mem_solG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:59.714243+00:00
-- url     : https://prove2.me/theorems/273f351a-3969-4e94-a9c1-f6aa677e32c0
-- title:
--   HCA: mem sol G
-- statement:
--   The HCA construction uses the mem sol G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsExpLieAlgebraComplexUnits.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsExpLieAlgebraComplexUnits.lean#L24-L32

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GroundTheory.Automorphic
open GlobalTheory GlobalTheory.HCA
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤)

theorem GlobalTheory.HCA.mem_solG {P : Polynomial ℂ} {f : G → ℂ} : f ∈ solG h b P ↔ ∃ hf : h.IsSmoothFun f,
    Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P
      (⟨f, hf⟩ : h.smoothFuns (F := ℂ)) = 0 := by sorry
