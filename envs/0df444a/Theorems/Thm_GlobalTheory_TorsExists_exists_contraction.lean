-- Prove2me | Theorems.Thm_GlobalTheory_TorsExists_exists_contraction
-- name    : GlobalTheory.TorsExists.exists_contraction
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:49.591528+00:00
-- url     : https://prove2.me/theorems/9dabd387-76b2-479f-839c-1fbba0c43b86
-- title:
--   Tors Exists: exists contraction
-- statement:
--   The Tors Exists construction uses the exists contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsIsUnitField.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsIsUnitField.lean#L43-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]

theorem GlobalTheory.TorsExists.exists_contraction {R : Type} [CommRing R] [IsLocalRing R] (D : Matrix Ix Ix R) (hD : D * D = 0)
    (hex : ∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 →
      ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) :
    ∃ h : Matrix Ix Ix R, D * h + h * D = 1 := by sorry
