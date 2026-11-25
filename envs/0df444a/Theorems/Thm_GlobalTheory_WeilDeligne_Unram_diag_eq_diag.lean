-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_Unram_diag_eq_diag
-- name    : GlobalTheory.WeilDeligne.Unram.diag_eq_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:01:00.975812+00:00
-- url     : https://prove2.me/theorems/b8c231cc-66de-4f20-979d-f8e2e9734af8
-- title:
--   Unram: diag eq diag
-- statement:
--   The Unram construction uses the diag eq diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L94-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
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
open GlobalTheory.WeilDeligne.Unram
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem GlobalTheory.WeilDeligne.Unram.diag_eq_diag {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → ℂˣ} {d : κ → ℂˣ}
    (hcd : (Finset.univ.val.map fun i => (c i : ℂ)) = Finset.univ.val.map fun k => (d k : ℂ)) :
    WD.mk (WDRep.diag h c) = WD.mk (WDRep.diag h d) := by sorry
