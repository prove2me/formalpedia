-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpTw_add
-- name    : GlobalTheory.WeilDeligne.WD.lpTw_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:02:49.833452+00:00
-- url     : https://prove2.me/theorems/37904818-88cc-4ca1-8bd5-206493be96d4
-- title:
--   WD: lp Tw add
-- statement:
--   The WD construction uses the lp Tw add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/Mono0OfLpDimEqOne.lean#L58-L64

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

theorem GlobalTheory.WeilDeligne.WD.lpTw_add (a : WD h) (s t : ℝ) : lpTw (lpTw a s) t = lpTw a (s + t) := by sorry
