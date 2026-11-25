-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_comm
-- name    : GlobalTheory.WeilDeligne.WD.lpSum_comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:05.112661+00:00
-- url     : https://prove2.me/theorems/45c4a458-4274-59b5-921d-65f097fe7b94
-- title:
--   WD: lp Sum comm
-- statement:
--   The WD construction uses the lp Sum comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L40-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.WD
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}

theorem GlobalTheory.WeilDeligne.WD.lpSum_comm (a b : WD h) : lpSum a b = lpSum b a := by sorry
