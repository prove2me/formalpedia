-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_iso_sum_tensor
-- name    : GlobalTheory.WeilDeligne.WDRep.iso_sum_tensor
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:27.419599+00:00
-- url     : https://prove2.me/theorems/210f1738-bf78-51e1-9662-a1d1645eb016
-- title:
--   WDRep: iso sum tensor
-- statement:
--   The WDRep construction uses the iso sum tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LpCharCompatibilities.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LpCharCompatibilities.lean#L18-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities
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
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
open GlobalTheory.WeilDeligne.WDRep

theorem GlobalTheory.WeilDeligne.WDRep.iso_sum_tensor (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.sum b).tensor c).Iso ((a.tensor c).sum (b.tensor c)) := by sorry
