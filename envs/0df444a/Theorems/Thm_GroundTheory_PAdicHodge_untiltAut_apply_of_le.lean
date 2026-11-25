-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_untiltAut_apply_of_le
-- name    : GroundTheory.PAdicHodge.untiltAut_apply_of_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:40.680053+00:00
-- url     : https://prove2.me/theorems/e0ab9dcd-855c-4fa0-8c96-b8dc993e19de
-- title:
--   PAdic Hodge: untilt Aut apply of le
-- statement:
--   The PAdic Hodge construction uses the untilt Aut apply of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L73-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L73-L107

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Definitions.Def_GroundTheory_PAdicHodge_FWNatural
import Theorems.Thm_GroundTheory_PAdicHodge_untiltField_mono

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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p

theorem GroundTheory.PAdicHodge.untiltAut_apply_of_le {M N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N] (h : M ≤ N)
    (σ : N ≃ₐ[K♭] N) (hσ : ∀ y : N, (y : C♭) ∈ M → σ y = y) (x : untiltField K C p M) :
    untiltAut N σ ⟨x, untiltField_mono h x.2⟩ = ⟨x, untiltField_mono h x.2⟩ := by sorry
