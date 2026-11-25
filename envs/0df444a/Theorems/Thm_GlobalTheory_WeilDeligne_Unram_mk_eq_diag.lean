-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_Unram_mk_eq_diag
-- name    : GlobalTheory.WeilDeligne.Unram.mk_eq_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:01.471936+00:00
-- url     : https://prove2.me/theorems/d2249dd6-f41d-52d9-a785-355ded88b189
-- title:
--   Unram: mk eq diag
-- statement:
--   The Unram construction uses the mk eq diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L57-L67

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

theorem GlobalTheory.WeilDeligne.Unram.mk_eq_diag {ι : Type*} [Finite ι] {a : WDRep h V} (ha : a.Unr) (b : Basis ι ℂ V)
    (c : ι → ℂˣ) (hb : ∀ i, a.ρ (frob h) (b i) = (c i : ℂ) • b i) :
    WD.mk a = WD.mk (WDRep.diag h c) := by sorry
