-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_evalB_toBDeRhamPlus
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.evalB_toBDeRhamPlus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:06.062272+00:00
-- url     : https://prove2.me/theorems/1e907b3b-6674-4d0e-b9e8-c215fe4d5c62
-- title:
--   Is Perfectoid Field: eval B to BDe Rham Plus
-- statement:
--   The Is Perfectoid Field construction uses the eval B to BDe Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean#L44-L48

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
omit [CharZero K]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.evalB_toBDeRhamPlus (n : ℕ) (a : 𝔸) :
    evalB K p n (toBDeRhamPlus 𝒪 p a) = Ideal.Quotient.mk (J ^ n) a := by sorry
