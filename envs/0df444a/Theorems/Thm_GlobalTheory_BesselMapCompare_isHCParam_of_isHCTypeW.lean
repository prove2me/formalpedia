-- Prove2me | Theorems.Thm_GlobalTheory_BesselMapCompare_isHCParam_of_isHCTypeW
-- name    : GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:03.321835+00:00
-- url     : https://prove2.me/theorems/1ed8434d-9e63-4437-bf44-d383056095de
-- title:
--   Bessel Map Compare: is HCParam of is HCType W
-- statement:
--   The Bessel Map Compare construction uses the is HCParam of is HCType W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBesselMapSmBesselCharIff.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsBesselMapSmBesselCharIff.lean#L28-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBesselMapSmBesselCharIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.BesselMapCompare
open PI.UpqRep GlobalTheory.IndefiniteRowSideFullHecke
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V)}
    (h : IsHCTypeW k r z u π) : PI.UpqRep.IsHCParam u := by sorry
