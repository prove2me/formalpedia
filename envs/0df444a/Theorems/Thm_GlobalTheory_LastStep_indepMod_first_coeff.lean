-- Prove2me | Theorems.Thm_GlobalTheory_LastStep_indepMod_first_coeff
-- name    : GlobalTheory.LastStep.indepMod_first_coeff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:21.75439+00:00
-- url     : https://prove2.me/theorems/1cd4c833-ca77-4808-9124-59c5f1bc6620
-- title:
--   Last Step: indep Mod first coeff
-- statement:
--   The Last Step construction uses the indep Mod first coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IndependentModFirstCoeffChainLastStep.lean#L43-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IndependentModFirstCoeffChainLastStep.lean#L43-L85

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IndependentModFirstCoeffChainLastStep
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot
open GlobalTheory GlobalTheory.LastStep

theorem GlobalTheory.LastStep.indepMod_first_coeff : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by sorry
