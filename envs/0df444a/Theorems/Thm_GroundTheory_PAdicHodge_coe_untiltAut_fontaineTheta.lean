-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coe_untiltAut_fontaineTheta
-- name    : GroundTheory.PAdicHodge.coe_untiltAut_fontaineTheta
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:10.557687+00:00
-- url     : https://prove2.me/theorems/d6c63885-4ca8-53a4-9329-b006b97b1df7
-- title:
--   PAdic Hodge: coe untilt Aut fontaine Theta
-- statement:
--   The PAdic Hodge construction uses the coe untilt Aut fontaine Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L126-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L126-L143

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
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
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.coe_untiltAut_fontaineTheta (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (u : WittVector p (integerTilt K C p N))
    (hu : ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) ∈ untiltField K C p N) :
    ((untiltAut N σ ⟨_, hu⟩ : untiltField K C p N) : C) =
      ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype
        (WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u)) :
        normInteger C) : C) := by sorry
