-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coe_untiltAut_of_le
-- name    : GroundTheory.PAdicHodge.coe_untiltAut_of_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:38.827075+00:00
-- url     : https://prove2.me/theorems/304a1975-a997-46cb-8fed-37afc6008295
-- title:
--   PAdic Hodge: coe untilt Aut of le
-- statement:
--   The PAdic Hodge construction uses the coe untilt Aut of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L26-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L26-L71

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

theorem GroundTheory.PAdicHodge.coe_untiltAut_of_le {N N' : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    [FiniteDimensional K♭ N'] (h : N ≤ N') (σ : N ≃ₐ[K♭] N) (σ' : N' ≃ₐ[K♭] N')
    (hσ : ∀ y : N, ((σ' ⟨y, h y.2⟩ : N') : C♭) = ((σ y : N) : C♭)) (x : untiltField K C p N) :
    ((untiltAut N' σ' ⟨x, untiltField_mono h x.2⟩ : untiltField K C p N') : C) =
      ((untiltAut N σ x : untiltField K C p N) : C) := by sorry
