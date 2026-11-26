-- Prove2me | Theorems.Thm_KrohnRhodes_cover_const_group
-- name    : KrohnRhodes.cover_const_group
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:43.207578+00:00
-- url     : https://prove2.me/theorems/dd82dd49-10a4-58a9-82d4-969d44c9cf6d
-- title:
--   Krohn Rhodes: cover const group
-- statement:
--   **Group-case cover family 2: constants are covered (uses inverses).** In the wreath product
--   of `cover_act_group`, every constant $\overline{x} \in \mathrm{End}(Q)$, $x \in Q$, is covered
--   (`Covers`) with respect to the decoding `groupProj`. This is the only one of the covers in
--   this file whose construction uses inverses (DKS Lemma 2.9, appendix, cover $(f_x, 1)$ with
--   $h f_x = x \cdot h^{-1}$, adapted to left actions); the group tower
--   (`group_subquotient_faithful_aux`, via the Krasner–Kaloujnine embedding) also uses the group
--   structure.
--
--   *Proof sketch.* Take $\hat{w} := (f_x, 1)$ with decoration
--   $f_x(m) := \overline{\, \mathrm{act}(m^{-1})(x)\,}$ (a constant of $\mathrm{End}(Q)$, hence in
--   the reset submonoid). Then $\hat{w} \bullet (q, m) = (\mathrm{act}(m^{-1})(x),\ m)$ and $\varphi
--   = \mathrm{act}(m)(\mathrm{act}(m^{-1})(x)) = \mathrm{act}(m m^{-1})(x) = x =
--   \overline{x}(\varphi(q,m))$ — the group inverse cancels. Direct computation.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L752-L765
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L752-L765

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

theorem KrohnRhodes.cover_const_group {G Q : Type} [Group G] (act : G →* Function.End Q) (x : Q) :
    ∃ w : WreathProduct ↥(resetSubmonoid Q) G G,
      Covers (groupProj act) w (constEnd x) := by sorry
