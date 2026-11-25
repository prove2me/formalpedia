-- Prove2me | Theorems.Thm_GlobalTheory_T_weilGroup_isSemisimple_of_semisimple_frob
-- name    : GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:23.026785+00:00
-- url     : https://prove2.me/theorems/456e74f2-5adf-5e1e-9a65-764c8a413816
-- title:
--   T: weil Group is Semisimple of semisimple frob
-- statement:
--   The T construction uses the weil Group is Semisimple of semisimple frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrobStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrobStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrob
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrobStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ φ : Weil h, deg φ = 1 → End.IsSemisimple (ρ φ) → ∀ σ : Weil h, End.IsSemisimple (ρ σ) := by sorry
