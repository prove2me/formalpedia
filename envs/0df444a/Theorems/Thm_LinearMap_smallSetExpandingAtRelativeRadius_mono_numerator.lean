-- Prove2me | Theorems.Thm_LinearMap_smallSetExpandingAtRelativeRadius_mono_numerator
-- name    : LinearMap.smallSetExpandingAtRelativeRadius_mono_numerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:39:32.867986+00:00
-- url     : https://prove2.me/theorems/14fa41ab-aa54-4f57-b7fc-d4f6efd984a1
-- title:
--   Linear Map: small Set Expanding At Relative Radius mono numerator
-- statement:
--   The Linear Map construction uses the small Set Expanding At Relative Radius mono numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/TannerExpansion.lean#L70-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/TannerExpansion.lean#L70-L86

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
set_option autoImplicit false
open LinearMap
open QEC.Coding
universe u v w

theorem LinearMap.smallSetExpandingAtRelativeRadius_mono_numerator
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    {f : Word F ι →ₗ[F] Word F κ}
    {smallNumerator largeNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hNumerator : smallNumerator ≤ largeNumerator)
    (hExpansion : f.SmallSetExpandingAtRelativeRadius
      largeNumerator radiusDenominator
      expansionNumerator expansionDenominator) :
    f.SmallSetExpandingAtRelativeRadius
      smallNumerator radiusDenominator
      expansionNumerator expansionDenominator := by sorry
