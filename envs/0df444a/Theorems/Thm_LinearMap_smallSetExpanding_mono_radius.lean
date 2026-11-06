-- Prove2me | Theorems.Thm_LinearMap_smallSetExpanding_mono_radius
-- name    : LinearMap.smallSetExpanding_mono_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:39:31.640359+00:00
-- url     : https://prove2.me/theorems/13ebb9da-eb7e-4f63-9fcf-c5b5122ae6e8
-- title:
--   Linear Map: small Set Expanding mono radius
-- statement:
--   The Linear Map construction uses the small Set Expanding mono radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/TannerExpansion.lean#L56-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/TannerExpansion.lean#L56-L68

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
set_option autoImplicit false
open LinearMap
open QEC.Coding
universe u v w

theorem LinearMap.smallSetExpanding_mono_radius
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    {f : Word F ι →ₗ[F] Word F κ}
    {smallRadius largeRadius expansionNumerator expansionDenominator : Nat}
    (hRadius : smallRadius ≤ largeRadius)
    (hExpansion : f.SmallSetExpanding
      largeRadius expansionNumerator expansionDenominator) :
    f.SmallSetExpanding
      smallRadius expansionNumerator expansionDenominator := by sorry
