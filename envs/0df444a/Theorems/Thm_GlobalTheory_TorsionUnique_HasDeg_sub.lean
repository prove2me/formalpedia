-- Prove2me | Theorems.Thm_GlobalTheory_TorsionUnique_HasDeg_sub
-- name    : GlobalTheory.TorsionUnique.HasDeg.sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:11.208586+00:00
-- url     : https://prove2.me/theorems/f12df8a1-554d-520b-8441-7235faa99c79
-- title:
--   Has Deg: sub
-- statement:
--   The Has Deg construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfVanish.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfVanish.lean#L23-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionUnique
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]
omit [Fintype Ix] [DecidableEq Ix]

theorem GlobalTheory.TorsionUnique.HasDeg.sub {deg : Ix → ℕ} {k : ℤ} {X Y : Matrix Ix Ix R}
    (hX : HasDeg deg k X) (hY : HasDeg deg k Y) : HasDeg deg k (X - Y) := by sorry
