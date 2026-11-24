-- Prove2me | Theorems.Thm_GlobalTheory_K4_TopW_isTopW_topW_of_exists
-- name    : GlobalTheory.K4.TopW.isTopW_topW_of_exists
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:41:25.98091+00:00
-- url     : https://prove2.me/theorems/f894a253-b847-48db-932d-c0063ba4c7c6
-- title:
--   Top W: is Top W top W of exists
-- statement:
--   The Top W construction uses the is Top W top W of exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsTopWTopWOfExists.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsTopWTopWOfExists.lean#L89-L93

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

theorem GlobalTheory.K4.TopW.isTopW_topW_of_exists {σ : Ω ≃ₐ[F] Ω} (h : ∃ w : K, IsTopW ζ x y η σ w) :
    IsTopW ζ x y η σ (topW (K := K) ζ x y η σ) := by sorry
