-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_psi_single_mul
-- name    : GlobalTheory.CompanionTheory.ProdSimple.psi_single_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:41.138872+00:00
-- url     : https://prove2.me/theorems/07192405-13ff-49c1-a835-d79ee993451b
-- title:
--   Prod Simple: psi single mul
-- statement:
--   The Prod Simple construction uses the psi single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L126-L133

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

theorem GlobalTheory.CompanionTheory.ProdSimple.psi_single_mul (ρ : Representation ℂ (∀ c, L c) W) (v : W) (g : ∀ c, L c)
    (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v (fun c => MonoidAlgebra.single (g c) (1 : ℂ) * x c) = ρ g (psi ρ v x) := by sorry
