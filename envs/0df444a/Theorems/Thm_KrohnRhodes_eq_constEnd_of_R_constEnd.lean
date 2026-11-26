-- Prove2me | Theorems.Thm_KrohnRhodes_eq_constEnd_of_R_constEnd
-- name    : KrohnRhodes.eq_constEnd_of_R_constEnd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:03.825557+00:00
-- url     : https://prove2.me/theorems/a4872e11-64e3-52c7-aef7-11ce473d1213
-- title:
--   Krohn Rhodes: eq const End of R const End
-- statement:
--   **Anything right-related to a constant map is that constant map.**  If
--   `Green.R (constEnd p) b` holds in `Function.End Q`, then `b = constEnd p`.
--   (`Green.R` provides `s` with `constEnd p * s = b`, and `constEnd p * s`
--   collapses to `constEnd p` by left absorption.)
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/ConstantMaps.lean#L95-L98
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/ConstantMaps.lean#L95-L98

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

theorem KrohnRhodes.eq_constEnd_of_R_constEnd {p : Q} {b : Function.End Q}
    (h : Green.R (constEnd p) b) : b = constEnd p := by sorry
