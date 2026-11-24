-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GreenbergWiles_exists_primitiveRoot_of_isAlgClosure
-- name    : GlobalTheory.CompanionTheory.GreenbergWiles.exists_primitiveRoot_of_isAlgClosure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:04.516741+00:00
-- url     : https://prove2.me/theorems/dc6b5f00-4fc5-47bc-a34a-bff284cefb24
-- title:
--   Greenberg Wiles: exists primitive Root of is Alg Closure
-- statement:
--   The Greenberg Wiles construction uses the exists primitive Root of is Alg Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsPrimitiveRootOfIsAlgClosure.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsPrimitiveRootOfIsAlgClosure.lean#L10-L15

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrimitiveRootOfIsAlgClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GreenbergWiles

theorem GlobalTheory.CompanionTheory.GreenbergWiles.exists_primitiveRoot_of_isAlgClosure (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ) (hn : 0 < n) : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by sorry
