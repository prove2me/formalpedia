-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ringHom_ext_bDeRhamPlus
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.ringHom_ext_bDeRhamPlus
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:25.116975+00:00
-- url     : https://prove2.me/theorems/ff20c18e-3471-439d-95f0-30c6f31e1ed1
-- title:
--   Is Perfectoid Field: ring Hom ext b De Rham Plus
-- statement:
--   The Is Perfectoid Field construction uses the ring Hom ext b De Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L94-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L94-L109

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
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
open Ideal WittVector IsLocalRing
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.ringHom_ext_bDeRhamPlus {F G : 𝔹 →+* 𝔹}
    (h : ∀ w : 𝕎𝒪♭, F (wittToBDeRhamPlus 𝒪 p w) = G (wittToBDeRhamPlus 𝒪 p w))
    (hF : ∀ x ∈ maximalIdeal 𝔹, F x ∈ maximalIdeal 𝔹)
    (hG : ∀ x ∈ maximalIdeal 𝔹, G x ∈ maximalIdeal 𝔹) : F = G := by sorry
