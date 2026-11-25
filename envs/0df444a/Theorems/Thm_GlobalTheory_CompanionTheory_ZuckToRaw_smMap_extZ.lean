-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_smMap_extZ
-- name    : GlobalTheory.CompanionTheory.ZuckToRaw.smMap_extZ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:21.107518+00:00
-- url     : https://prove2.me/theorems/56978d33-3d15-582e-9711-29823c1fc91b
-- title:
--   Zuck To Raw: sm Map ext Z
-- statement:
--   The Zuck To Raw construction uses the sm Map ext Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L32-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L32-L58

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckToRaw
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckToRaw.smMap_extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub)
    (hf : ∀ W, LieWd k r W → ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))), (∀ W' ∈ Ws, LieWd k r W') ∧
      ∀ y : R.smSub, ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (f y : R'.H)‖ ≤
        C * (Ws.map fun W' => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W' (y : R.H)‖).sum) :
    SmMap R R' (extZ f) := by sorry
