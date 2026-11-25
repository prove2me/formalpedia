-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpTw_sum
-- name    : GlobalTheory.WeilDeligne.WD.lpTw_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:02:23.091896+00:00
-- url     : https://prove2.me/theorems/050c37b6-1ccf-412e-8d58-7fc8103e2a90
-- title:
--   WD: lp Tw sum
-- statement:
--   The WD construction uses the lp Tw sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L66-L70

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

theorem GlobalTheory.WeilDeligne.WD.lpTw_sum (a b : WD h) (s : ℝ) : lpTw (lpSum a b) s = lpSum (lpTw a s) (lpTw b s) := by sorry
