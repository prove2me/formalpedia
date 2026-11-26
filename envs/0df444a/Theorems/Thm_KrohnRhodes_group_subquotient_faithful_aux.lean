-- Prove2me | Theorems.Thm_KrohnRhodes_group_subquotient_faithful_aux
-- name    : KrohnRhodes.group_subquotient_faithful_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:50.428426+00:00
-- url     : https://prove2.me/theorems/e19522b3-4347-48d3-86cb-420c4dcf81e7
-- title:
--   Krohn Rhodes: group subquotient faithful aux
-- statement:
--   **Subquotient-faithful Krohn-Rhodes for finite groups.** Every finite group
--       `G` with `Nat.card G ≤ n` has a factor tower in which every factor divides `G`
--       (`KRFactorTowerSub G`); the construction uses only simple-group factors, but the
--       statement does not record this.  Proved by strong
--       induction on `Nat.card G`, peeling a proper normal subgroup `N` and recursing
--       on the subgroup `↥N` (`÷ G`) and the quotient `G/N` (`÷ G`), threading the
--       `MonoidDivides`-to-`G` witness through every factor (subgroup-divides /
--       quotient-divides + transitivity).
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L512-L570
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean#L512-L570

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
open KrohnRhodes
open Green

theorem KrohnRhodes.group_subquotient_faithful_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G ≤ n →
      Nonempty (KRFactorTowerSub G) := by sorry
