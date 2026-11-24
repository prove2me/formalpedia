-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothModule_adj_ext
-- name    : GlobalTheory.CompanionTheory.SmoothModule.adj_ext
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:26.744778+00:00
-- url     : https://prove2.me/theorems/f58f3740-6275-448d-85bc-7b8caa0f8f1d
-- title:
--   Smooth Module: adj ext
-- statement:
--   The Smooth Module construction uses the adj ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L246-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/GlRelOfBracket.lean#L246-L254

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_GlRelOfBracket
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep (IsURepOn UJset inG)
open PI.DSInfCharCap (dsigC thetaJ)
open PI.PhMeasCore (dsig smoothVecs)
open Formalism.REAL (Jm)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothModule
variable {n : ℕ} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.SmoothModule.adj_ext {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V)
    (h : ∀ X, inG ε X → ∀ x y, ⟪C X x, y⟫_ℂ = -⟪x, C X y⟫_ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (x y : V) :
    ⟪C Y x, y⟫_ℂ = -⟪x, C (thetaJ ε Y) y⟫_ℂ := by sorry
