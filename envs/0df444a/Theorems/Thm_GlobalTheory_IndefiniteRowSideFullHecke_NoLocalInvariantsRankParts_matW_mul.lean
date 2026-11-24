-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NoLocalInvariantsRankParts_matW_mul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:35.907701+00:00
-- url     : https://prove2.me/theorems/f7d6f6a2-725d-4c53-93c2-181a84319c7a
-- title:
--   No Local Invariants Rank Parts: mat W mul
-- statement:
--   The No Local Invariants Rank Parts construction uses the mat W mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/NoLocalInvariants.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/NoLocalInvariants.lean#L59-L62

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW_mul (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g h : G H.E N.Om) :
    matW N i ρ (g * h) = matW N i ρ g * matW N i ρ h := by sorry
