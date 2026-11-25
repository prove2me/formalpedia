-- Prove2me | Theorems.Thm_GroundTheory_Global_isElliptic_of_map_eq
-- name    : GroundTheory.Global.isElliptic_of_map_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:20.349203+00:00
-- url     : https://prove2.me/theorems/47c5a59d-9390-4138-b464-2f88ed637288
-- title:
--   Global: is Elliptic of map eq
-- statement:
--   The Global construction uses the is Elliptic of map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L21-L30

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]

theorem GroundTheory.Global.isElliptic_of_map_eq {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L} [E.IsElliptic]
    {W : WeierstrassCurve (localizationAt L v)} (h : W.map (algebraMap (localizationAt L v) L) = E)
    (hΔ : E.Δ⁻¹ ∈ localizationAt L v) : W.IsElliptic := by sorry
