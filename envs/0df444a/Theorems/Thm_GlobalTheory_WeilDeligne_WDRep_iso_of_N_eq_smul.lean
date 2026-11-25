-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_iso_of_N_eq_smul
-- name    : GlobalTheory.WeilDeligne.WDRep.iso_of_N_eq_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:35.091648+00:00
-- url     : https://prove2.me/theorems/f0550a3c-cd72-41e4-ad8b-11856ee346ba
-- title:
--   WDRep: iso of N eq smul
-- statement:
--   The WDRep construction uses the iso of N eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAevalEqSmulOnEigenspace.lean#L93-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAevalEqSmulOnEigenspace.lean#L93-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
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

theorem GlobalTheory.WeilDeligne.WDRep.iso_of_N_eq_smul : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a b : _root_.GlobalTheory.WeilDeligne.WDRep h V) (c : ℂ), c ≠ 0 → a.ρ = b.ρ →
    b.N = c • a.N → a.Iso b := by sorry
