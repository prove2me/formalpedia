-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_of_isSemisimple_frob
-- name    : GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:06:13.218972+00:00
-- url     : https://prove2.me/theorems/bc411ca1-abff-46c4-9d40-dea74551d32a
-- title:
--   Weil Deligne: is Semisimple of is Semisimple frob
-- statement:
--   The Weil Deligne construction uses the is Semisimple of is Semisimple frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrob.lean#L100-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrob.lean#L100-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
open NumberField IsDedekindDomain Polynomial Module

theorem GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
      _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ φ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg φ = 1 →
      End.IsSemisimple (ρ φ) → ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, End.IsSemisimple (ρ σ) := by sorry
