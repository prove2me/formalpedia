-- Prove2me | Theorems.Thm_GlobalTheory_NB_LT_algHom_ext_X
-- name    : GlobalTheory.NB.LT.algHom_ext_X
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:37.174011+00:00
-- url     : https://prove2.me/theorems/bd2f60ab-e5fb-4846-8c8f-3032a821a3cd
-- title:
--   LT: alg Hom ext X
-- statement:
--   The LT construction uses the alg Hom ext X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L111-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}

theorem GlobalTheory.NB.LT.algHom_ext_X (σ τ : R⟦X⟧ →ₐ[R] R⟦X⟧) (h : σ X = τ X) (hX : X ∣ σ X) : σ = τ := by sorry
