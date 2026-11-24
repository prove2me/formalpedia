-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinRep_asAlgebraHom_leftRep
-- name    : GlobalTheory.CompanionTheory.FinRep.asAlgebraHom_leftRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:18.257808+00:00
-- url     : https://prove2.me/theorems/9594f734-5831-43ad-b5c7-fd0b2bb39a3d
-- title:
--   Fin Rep: as Algebra Hom left Rep
-- statement:
--   The Fin Rep construction uses the as Algebra Hom left Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeparableIrreducible.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeparableIrreducible.lean#L30-L35

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinRep
variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem GlobalTheory.CompanionTheory.FinRep.asAlgebraHom_leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    (x : MonoidAlgebra ℂ Γ) (n : N) : Representation.asAlgebraHom (leftRep N) x n = x • n := by sorry
