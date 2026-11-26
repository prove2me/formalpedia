-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_gal_smul_dpow
-- name    : GroundTheory.PAdicHodge.ACris.gal_smul_dpow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:41.565152+00:00
-- url     : https://prove2.me/theorems/ab8f0bdf-d35d-538b-aefe-4f5382db9445
-- title:
--   ACris: gal smul dpow
-- statement:
--   The ACris construction uses the gal smul dpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L186-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L186-L190

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)

theorem GroundTheory.PAdicHodge.ACris.gal_smul_dpow (σ : Gal(PadicAlgCl p/K)) {x : AInf ℂ_[p] p} (hx : x ∈ RingHom.ker θ)
    (n : ℕ) :
    σ • (⟨dpow n x, dpow_mem hx n⟩ : ACrisZero ℂ_[p] p) =
      ⟨dpow n (σ • x), dpow_mem (gal_smul_mem_ker σ hx) n⟩ := by sorry
