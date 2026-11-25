-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_inv_sq_le_wP
-- name    : GlobalTheory.WigSh.inv_sq_le_wP
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:50.155426+00:00
-- url     : https://prove2.me/theorems/0a25b7d9-ccd8-4dd2-8f00-f163775694ef
-- title:
--   Wig Sh: inv sq le w P
-- statement:
--   The Wig Sh construction uses the inv sq le w P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvSqLeWignerCoeffSqRaising.lean#L35-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvSqLeWignerCoeffSqRaising.lean#L35-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqRaising
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh

theorem GlobalTheory.WigSh.inv_sq_le_wP (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hL : StrictAnti L) (hM : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l + 1) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hn : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ wP L M l := by sorry
