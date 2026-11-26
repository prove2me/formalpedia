-- Prove2me | Theorems.Thm_KrohnRhodes_isAperiodicElem_of_id_or_const
-- name    : KrohnRhodes.isAperiodicElem_of_id_or_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:42.620806+00:00
-- url     : https://prove2.me/theorems/337f29a4-5493-5da4-ad65-2b5066dd97bb
-- title:
--   Krohn Rhodes: is Aperiodic Elem of id or const
-- statement:
--   **A constants-plus-identity transformation monoid is aperiodic.**  Let
--   `S` be a submonoid of `Function.End Q` such that every element of `S` is
--   *either the identity or a constant map* (`hS`).  Then every element of `S`
--   is aperiodic: any two `H`-related elements `a, b ∈ S` are equal.
--
--   Proof by cases on `a`:
--   * if `a` is constant, `H a b` gives `Green.R a b`, so
--     `eq_constEnd_of_R_constEnd` forces `b = a`;
--   * if `a = 1`, `H 1 b` gives `Green.R 1 b`, providing `t` with
--     `(1 : Function.End Q) * t = b` *and* `b * t' = 1`.  If `b` is also `1`
--     we are done; if `b` is a constant `constEnd q`, then `b * t' = constEnd q`
--     by left absorption, so `constEnd q = 1`, i.e. `Q` is subsingleton, and
--     then `Function.End Q` is subsingleton so `a = b` regardless.
--
--   The conclusion is stated with `H` unfolded into explicit `L`- and `R`-witnesses.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/ConstantMaps.lean#L123-L159
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/ConstantMaps.lean#L123-L159

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.show false
open KrohnRhodes
universe u
variable {Q : Type u}

theorem KrohnRhodes.isAperiodicElem_of_id_or_const
    (S : Submonoid (Function.End Q))
    (hS : ∀ t ∈ S, t = 1 ∨ IsConstEnd t) :
    ∀ a b : S,
      ((∃ s t : S, s * a = b ∧ t * b = a) ∧
       (∃ s t : S, a * s = b ∧ b * t = a)) → a = b := by sorry
