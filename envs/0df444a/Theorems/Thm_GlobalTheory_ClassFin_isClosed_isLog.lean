-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_isClosed_isLog
-- name    : GlobalTheory.ClassFin.isClosed_isLog
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:35.888262+00:00
-- url     : https://prove2.me/theorems/ade55b00-08fe-4205-84a8-fe7fb2b144ef
-- title:
--   Class Fin: is Closed is Log
-- statement:
--   The Class Fin construction uses the is Closed is Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsClosedIsHermitianLogOfPosDef.lean#L8-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsClosedIsHermitianLogOfPosDef.lean#L8-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin

theorem GlobalTheory.ClassFin.isClosed_isLog : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by sorry
