-- Prove2me | Theorems.Thm_GwExact_rup_sound
-- name    : GwExact.rup_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:15.754147+00:00
-- url     : https://prove2.me/theorems/94195460-3d19-457e-9165-301d2b08b6c4
-- title:
--   Gw Exact: rup sound
-- statement:
--   Soundness of reverse unit propagation: if every clause from `src` is true under `σ` and `σ`
--   agrees with the partial assignment `(t, f)`, the propagation cannot reach a conflict.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L254-L348
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L254-L348

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.rup_sound {σ : Nat → Bool} {src : Nat → Option Cls} {w wm : Nat}
    (hsrc : ∀ h c, src h = some c → c.Holds σ) :
    ∀ cnt code t f, rup src w wm cnt code t f = true →
      (∀ v, t.testBit v = true → σ v = true) → (∀ v, f.testBit v = true → σ v = false) → False := by sorry
