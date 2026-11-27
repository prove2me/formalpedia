-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_exists_ofMatrix
-- name    : GlobalTheory.WeilDeligne.WD.exists_ofMatrix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:51:33.952167+00:00
-- url     : https://prove2.me/theorems/12e908d9-513a-5b76-b05f-093dcb75f02c
-- title:
--   WD: exists of Matrix
-- statement:
--   The WD construction uses the exists of Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L415-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L415-L433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
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
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
open GlobalTheory.WeilDeligne.WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem GlobalTheory.WeilDeligne.WD.exists_ofMatrix (x : WD h) : ∃ (n : ℕ) (ρ : Weil h →* GL (Fin n) ℂ)
    (N : Matrix (Fin n) (Fin n) ℂ) (h1 : _) (h2 : _) (h3 : _) (h4 : _),
    mk (WDRep.ofMatrix ρ N h1 h2 h3 h4) = x := by sorry
