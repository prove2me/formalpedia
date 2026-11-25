-- Prove2me | Theorems.Thm_GlobalTheory_K4_TopW_edge_inv
-- name    : GlobalTheory.K4.TopW.edge_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:58.723851+00:00
-- url     : https://prove2.me/theorems/6221916f-3986-47e5-a629-2eda26899f5c
-- title:
--   Top W: edge inv
-- statement:
--   The Top W construction uses the edge inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsTopWTopWOfExists.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsTopWTopWOfExists.lean#L84-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CobOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsFirstChernClassOfLineBundle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K4
open GlobalTheory.KEdge GlobalTheory.NeedB
variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
open GlobalTheory.K4.TopW
variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}

theorem GlobalTheory.K4.TopW.edge_inv {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) :
    edge x y η σ⁻¹ h = η (σ⁻¹ * h * σ) - η h + (x h).toAdd * (y σ).toAdd - (x σ).toAdd * (y h).toAdd := by sorry
