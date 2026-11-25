-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_Unram_exists_equiv_of_map_eq
-- name    : GlobalTheory.WeilDeligne.Unram.exists_equiv_of_map_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:02.259495+00:00
-- url     : https://prove2.me/theorems/1c820127-590c-52f1-bf01-99fbbefcfdf9
-- title:
--   Unram: exists equiv of map eq
-- statement:
--   The Unram construction uses the exists equiv of map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEquivOfMapEq.lean#L82-L92

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

theorem GlobalTheory.WeilDeligne.Unram.exists_equiv_of_map_eq {ι κ α : Type*} [Fintype ι] [Fintype κ] {c : ι → α} {d : κ → α}
    (hcd : Finset.univ.val.map c = Finset.univ.val.map d) : ∃ e : ι ≃ κ, ∀ i, d (e i) = c i := by sorry
