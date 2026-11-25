-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTransport_dot_expand
-- name    : GlobalTheory.CompanionTheory.ZuckTransport.dot_expand
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:18:09.864718+00:00
-- url     : https://prove2.me/theorems/788fea68-34b6-5098-bb7f-2b60315a82b9
-- title:
--   Zuck Transport: dot expand
-- statement:
--   The Zuck Transport construction uses the dot expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZuckermanHypothesis.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZuckermanHypothesis.lean#L18-L22

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesis
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckTransport
open PI.UpqRep CompanionTheory.LimBd.SchurHpk

theorem GlobalTheory.CompanionTheory.ZuckTransport.dot_expand {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ (a *ᵥ x) = ∑ p : Fin n × Fin n, u p.1 * x p.2 * a p.1 p.2 := by sorry
