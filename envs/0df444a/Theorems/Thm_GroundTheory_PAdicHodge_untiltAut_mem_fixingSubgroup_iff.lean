-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_untiltAut_mem_fixingSubgroup_iff
-- name    : GroundTheory.PAdicHodge.untiltAut_mem_fixingSubgroup_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:14.596317+00:00
-- url     : https://prove2.me/theorems/2cfc86b0-a901-4239-8573-b8d408f40ec7
-- title:
--   PAdic Hodge: untilt Aut mem fixing Subgroup iff
-- statement:
--   The PAdic Hodge construction uses the untilt Aut mem fixing Subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L114-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L114-L152

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

theorem GroundTheory.PAdicHodge.untiltAut_mem_fixingSubgroup_iff (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] {M : IntermediateField K♭ C♭} (h : M ≤ N) (σ : N ≃ₐ[K♭] N) :
    untiltAut N σ ∈ (IntermediateField.restrict (untiltField_mono (K := K) (p := p) h)).fixingSubgroup ↔
      σ ∈ (IntermediateField.restrict h).fixingSubgroup := by sorry
