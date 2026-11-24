-- Prove2me | Theorems.Thm_GlobalTheory_TorsionUnique_torsSq_unique
-- name    : GlobalTheory.TorsionUnique.torsSq_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:54.084027+00:00
-- url     : https://prove2.me/theorems/0a931bf7-48cf-4f82-9627-14b64defcd0b
-- title:
--   Torsion Unique: tors Sq unique
-- statement:
--   The Torsion Unique construction uses the tors Sq unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfVanish.lean#L179-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfVanish.lean#L179-L239

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
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]

theorem GlobalTheory.TorsionUnique.torsSq_unique : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix]
    (deg : Ix → ℕ) (D : Matrix Ix Ix R) (t t' : R),
    _root_.GlobalTheory.KeyKa.IsCx deg D → _root_.GlobalTheory.KeyKa.TorsSq deg D t →
      _root_.GlobalTheory.KeyKa.TorsSq deg D t' → t = t' ∧ IsUnit t := by sorry
