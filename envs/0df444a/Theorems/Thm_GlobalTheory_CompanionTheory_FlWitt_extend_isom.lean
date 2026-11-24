-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_extend_isom
-- name    : GlobalTheory.CompanionTheory.FlWitt.extend_isom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:41:24.029874+00:00
-- url     : https://prove2.me/theorems/05931b2a-3ad5-4f8f-80d0-b95dc78a258c
-- title:
--   Fl Witt: extend isom
-- statement:
--   The Fl Witt construction uses the extend isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L101-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean#L101-L119

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlWitt
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}

theorem GlobalTheory.CompanionTheory.FlWitt.extend_isom [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (U : Submodule L V) (φ : U →ₗ[L] V) (hinj : Function.Injective φ)
    (hiso : ∀ x y : U, h (φ x) (φ y) = h x y) :
    ∃ g : V ≃ₗ[L] V, IsIso h g ∧ ∀ x : U, g x = φ x := by sorry
