-- Prove2me | Theorems.Thm_GlobalTheory_SepPoint_isIntegrallyClosed_adjoin
-- name    : GlobalTheory.SepPoint.isIntegrallyClosed_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:14.624142+00:00
-- url     : https://prove2.me/theorems/4429a99f-2fc3-4f48-bbac-62dbe35ab9a2
-- title:
--   Sep Point: is Integrally Closed adjoin
-- statement:
--   The Sep Point construction uses the is Integrally Closed adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegrallyClosedAdjoin.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegrallyClosedAdjoin.lean#L10-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SepPoint

theorem GlobalTheory.SepPoint.isIntegrallyClosed_adjoin (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := by sorry
