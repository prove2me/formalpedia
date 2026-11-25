-- Prove2me | Theorems.Thm_GlobalTheory_K4_TopW_edge_mul_conj
-- name    : GlobalTheory.K4.TopW.edge_mul_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:53.924273+00:00
-- url     : https://prove2.me/theorems/43cdb331-9446-4443-8bde-da467fe97eb0
-- title:
--   Top W: edge mul conj
-- statement:
--   The Top W construction uses the edge mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsTopWTopWOfExists.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsTopWTopWOfExists.lean#L78-L82

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

theorem GlobalTheory.K4.TopW.edge_mul_conj {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ τ h : Γ) :
    edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h := by sorry
