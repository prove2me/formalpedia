-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_integerTiltHom_comp
-- name    : GroundTheory.PAdicHodge.integerTiltHom_comp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:08:00.538372+00:00
-- url     : https://prove2.me/theorems/b3af52b1-09e2-4aba-8df6-8f3be46bb0e3
-- title:
--   PAdic Hodge: integer Tilt Hom comp
-- statement:
--   The PAdic Hodge construction uses the integer Tilt Hom comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGalois.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGalois.lean#L88-L99

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
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

theorem GroundTheory.PAdicHodge.integerTiltHom_comp (N : IntermediateField K♭ C♭) (σ τ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖)
    (hτ : ∀ x : N, ‖((τ x : N) : C♭)‖ = ‖(x : C♭)‖)
    (hστ : ∀ x : N, ‖(((σ.comp τ) x : N) : C♭)‖ = ‖(x : C♭)‖) :
    integerTiltHom N (σ.comp τ) hστ = (integerTiltHom N σ hσ).comp (integerTiltHom N τ hτ) := by sorry
