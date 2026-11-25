-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_gp_apply
-- name    : GlobalTheory.CompanionTheory.NerveCoh.gp_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:14.279864+00:00
-- url     : https://prove2.me/theorems/c1e1e053-6f55-59b0-9b65-137d1adaf952
-- title:
--   Nerve Coh: gp apply
-- statement:
--   The Nerve Coh construction uses the gp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L218-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L218-L220

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
variable {C : Type} [Category.{0} C]

theorem GlobalTheory.CompanionTheory.NerveCoh.gp_apply (F : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : MCn F m)
    (c : Fin (n + 1) ⥤ C) : gp F θ f c =
      F.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) := by sorry
