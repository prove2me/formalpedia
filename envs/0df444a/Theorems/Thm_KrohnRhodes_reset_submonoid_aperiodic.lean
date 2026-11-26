-- Prove2me | Theorems.Thm_KrohnRhodes_reset_submonoid_aperiodic
-- name    : KrohnRhodes.reset_submonoid_aperiodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:22.876076+00:00
-- url     : https://prove2.me/theorems/9463fa57-58f9-59a0-93ae-2c344cb4d9b3
-- title:
--   Krohn Rhodes: reset submonoid aperiodic
-- statement:
--   **The reset submonoid is aperiodic.** Every element of the reset submonoid `resetSubmonoid`
--   of $\mathrm{End}(Q)$, viewed as a monoid in its own right, is aperiodic in the sense of
--   Green's relations (`Green.IsAperiodicElem`): its $\mathcal{H}$-class inside the submonoid is
--   trivial — $a \mathrel{\mathcal{H}} b$ implies $a = b$. This witnesses the reset factor of the
--   decomposition as a genuine aperiodic factor (the reset monoid `U_X` of DKS §2.4 consists of
--   idempotents).
--
--   *Proof sketch.* By `mem_reset_submonoid` every member of the submonoid is the identity or a
--   constant, so `isAperiodicElem_of_id_or_const` applies; its conclusion
--   is exactly the $\mathcal{H}$-triviality shape obtained by unfolding `Green.H` (an
--   $\mathcal{L}$-witness pair and an $\mathcal{R}$-witness pair in the subtype monoid) — destructure
--   the $\mathcal{H}$ hypothesis and apply.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L115-L119
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L115-L119

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green

theorem KrohnRhodes.reset_submonoid_aperiodic (Q : Type) :
    ∀ a : ↥(resetSubmonoid Q), IsAperiodicElem a := by sorry
