-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
-- name    : GlobalTheory.PDivGroup.rigLevel_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:38:46.546029+00:00
-- url     : https://prove2.me/theorems/d9cb1e5f-bcba-4481-8f49-475a574fa039
-- title:
--   PDiv Group: rig Level mk
-- statement:
--   The PDiv Group construction uses the rig Level mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L204-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L204-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem GlobalTheory.PDivGroup.rigLevel_mk (n : ℕ) (c : G.cocycles) (w : G.omega) :
    G.rigLevel n (G.rigMk (c, w)) = Submodule.Quotient.mk (⟨c.1 n, (c.2 n).1⟩, w.1 n) := by sorry

attribute [defeq] GlobalTheory.PDivGroup.rigLevel_mk
