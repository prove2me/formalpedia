-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmallBlockEigenvalues_one_lt_normV
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.one_lt_normV
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:19.46408+00:00
-- url     : https://prove2.me/theorems/53da5c60-6af3-47ab-8ff4-56b2e4c00e9f
-- title:
--   Small Block Eigenvalues: one lt norm V
-- statement:
--   The Small Block Eigenvalues construction uses the one lt norm V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/SmallRowEigenvalues.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/SmallRowEigenvalues.lean#L16-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_SmallRowEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.one_lt_normV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by sorry
