-- Prove2me | Theorems.Thm_GlobalTheory_LocFreeProj_finite_projective_of_locally_free
-- name    : GlobalTheory.LocFreeProj.finite_projective_of_locally_free
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:44.193036+00:00
-- url     : https://prove2.me/theorems/7ee1aca3-ac24-441a-8bb3-261907f59191
-- title:
--   Loc Free Proj: finite projective of locally free
-- statement:
--   The Loc Free Proj construction uses the finite projective of locally free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfLocallyFiniteFreeLocalizations.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfLocallyFiniteFreeLocalizations.lean#L7-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfLocallyFiniteFreeLocalizations
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
open GlobalTheory GlobalTheory.LocFreeProj

theorem GlobalTheory.LocFreeProj.finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by sorry
