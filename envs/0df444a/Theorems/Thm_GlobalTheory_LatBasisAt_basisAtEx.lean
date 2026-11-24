-- Prove2me | Theorems.Thm_GlobalTheory_LatBasisAt_basisAtEx
-- name    : GlobalTheory.LatBasisAt.basisAtEx
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:23.833655+00:00
-- url     : https://prove2.me/theorems/718f2d7d-7512-4751-8525-e4276f215142
-- title:
--   Lat Basis At: basis At Ex
-- statement:
--   The Lat Basis At construction uses the basis At Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L66-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L66-L105

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.LatBasisAt
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.LatBasisAt.basisAtEx : Formalism.L2.DIV.BasisAtEx := by sorry
