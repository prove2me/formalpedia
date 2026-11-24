-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_WordBlockPolynomials_iteratedFDeriv_directions_comp_perm_of_analyticAt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.iteratedFDeriv_directions_comp_perm_of_analyticAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:50.91573+00:00
-- url     : https://prove2.me/theorems/5d410bf0-6aad-4fc4-b059-6094cf668e87
-- title:
--   Word Block Polynomials: iterated FDeriv directions comp perm of analytic At
-- statement:
--   The Word Block Polynomials construction uses the iterated FDeriv directions comp perm of analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/WordDerivativeBlocks.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/WordDerivativeBlocks.lean#L100-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.iteratedFDeriv_directions_comp_perm_of_analyticAt (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {k : ℕ} (u v : Fin k → Λ) (σ : Equiv.Perm (Fin k)) (h : u = v ∘ σ) :
    iteratedFDeriv ℂ k F p (fun j => dir (u j)) = iteratedFDeriv ℂ k F p (fun j => dir (v j)) := by sorry
