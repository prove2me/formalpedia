-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_map_mem_maximalIdeal_pow
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.map_mem_maximalIdeal_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:05.657566+00:00
-- url     : https://prove2.me/theorems/f2462a84-acdb-4677-a2b8-ae44b0d6cea8
-- title:
--   Is Perfectoid Field: map mem maximal Ideal pow
-- statement:
--   The Is Perfectoid Field construction uses the map mem maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L79-L85

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.map_mem_maximalIdeal_pow {F : 𝔹 →+* 𝔹} (hF : ∀ x ∈ maximalIdeal 𝔹, F x ∈ maximalIdeal 𝔹)
    {x : 𝔹} {n : ℕ} (hx : x ∈ maximalIdeal 𝔹 ^ n) : F x ∈ maximalIdeal 𝔹 ^ n := by sorry
