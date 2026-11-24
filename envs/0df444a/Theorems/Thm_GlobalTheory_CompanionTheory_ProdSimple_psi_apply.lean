-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_psi_apply
-- name    : GlobalTheory.CompanionTheory.ProdSimple.psi_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:00.006646+00:00
-- url     : https://prove2.me/theorems/52886b4a-9888-45cc-bc3c-6fdd35ef4f67
-- title:
--   Prod Simple: psi apply
-- statement:
--   The Prod Simple construction uses the psi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L108-L110

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple
variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.ProdSimple.psi_apply (ρ : Representation ℂ (∀ c, L c) W) (v : W) (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v x = ∑ g : ∀ c, L c, (∏ c, (x c).coeff (g c)) • ρ g v := by sorry
