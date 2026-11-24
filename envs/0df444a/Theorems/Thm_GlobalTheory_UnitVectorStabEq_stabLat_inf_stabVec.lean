-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabEq_stabLat_inf_stabVec
-- name    : GlobalTheory.UnitVectorStabEq.stabLat_inf_stabVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:01.532419+00:00
-- url     : https://prove2.me/theorems/6c39ee0d-f7c6-4a57-8f16-f5f26926fbd2
-- title:
--   Unit Vector Stab Eq: stab Lat inf stab Vec
-- statement:
--   The Unit Vector Stab Eq construction uses the stab Lat inf stab Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L84-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L84-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabEq

theorem GlobalTheory.UnitVectorStabEq.stabLat_inf_stabVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), IsSDLat σ J v L → ∀ x ∈ L, (∃ b ∈ OEv F E v, hR (Fv F v) σ J x x * b = 1) → stabLat σ J v L ⊓ stabVec σ J v x = stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x := by sorry
