-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NoLocalInvariantsRankParts_matT_transpose_mul_matW
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT_transpose_mul_matW
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:00.630086+00:00
-- url     : https://prove2.me/theorems/edadb367-e025-5621-af46-79267bfc3d9a
-- title:
--   No Local Invariants Rank Parts: mat T transpose mul mat W
-- statement:
--   The No Local Invariants Rank Parts construction uses the mat T transpose mul mat W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/NoLocalInvariants.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/NoLocalInvariants.lean#L67-L73

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT_transpose_mul_matW (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (g : G H.E N.Om) :
    (matT N i ρ g)ᵀ * matW N i ρ g =
      algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • (1 : Matrix _ _ (Kf N i)) := by sorry
