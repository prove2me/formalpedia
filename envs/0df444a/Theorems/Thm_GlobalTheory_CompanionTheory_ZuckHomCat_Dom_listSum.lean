-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckHomCat_Dom_listSum
-- name    : GlobalTheory.CompanionTheory.ZuckHomCat.Dom.listSum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:07.560231+00:00
-- url     : https://prove2.me/theorems/49d73806-79ac-4e67-9de8-1ffa854739b5
-- title:
--   Dom: list Sum
-- statement:
--   The Dom construction uses the list Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L77-L82

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckHomCat.Dom.listSum {X : Obj k r} {ι : Type} (φ : ι → M X → ℝ) :
    ∀ l : List ι, (∀ i ∈ l, Dom X (φ i)) → Dom X fun x => (l.map fun i => φ i x).sum
  := by sorry
