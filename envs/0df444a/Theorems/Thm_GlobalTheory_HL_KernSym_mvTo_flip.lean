-- Prove2me | Theorems.Thm_GlobalTheory_HL_KernSym_mvTo_flip
-- name    : GlobalTheory.HL.KernSym.mvTo_flip
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:35.537797+00:00
-- url     : https://prove2.me/theorems/eb37ed6b-8b0a-44fb-ab81-e8db1a067f50
-- title:
--   Kern Sym: mv To flip
-- statement:
--   The Kern Sym construction uses the mv To flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMoveKernelSymm.lean#L67-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMoveKernelSymm.lean#L67-L82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMoveTermWeightCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralTransportAndChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesReferenceSubgroupsRelIndexEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMoveKernelSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.KernSym
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.KernSym.mvTo_flip (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ Λ' : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ) (hF' : S.InFF β (j + 1) βJ d Λ')
    (w : S.MW) (hw : S.MvTo (j + 1) d Λ Λ' w) : S.MvTo (j + 1) d Λ' Λ (w.1, -w.2) := by sorry
