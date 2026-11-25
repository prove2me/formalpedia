-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_ds_map
-- name    : GlobalTheory.CompanionTheory.ZuckUIso.ds_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:56.789591+00:00
-- url     : https://prove2.me/theorems/be20aea6-7cd6-51f4-8a50-7b11bd52a279
-- title:
--   Zuck UIso: ds map
-- statement:
--   The Zuck UIso construction uses the ds map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UnitaryIso.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UnitaryIso.lean#L26-L32

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckUIso
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H'] [NormedSpace ℂ H']
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}

theorem GlobalTheory.CompanionTheory.ZuckUIso.ds_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : ds σ' X (e v) = e (ds σ X v) := by sorry
