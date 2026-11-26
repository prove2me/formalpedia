-- Prove2me | Theorems.Thm_KrohnRhodes_cover_act_group
-- name    : KrohnRhodes.cover_act_group
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:35.655121+00:00
-- url     : https://prove2.me/theorems/a281369d-ec3a-4912-b2d4-51e732bc3dbf
-- title:
--   Krohn Rhodes: cover act group
-- statement:
--   **Group-case cover family 1: group translations are covered.** In the wreath product
--   $U(Q) \wr_G G$ — decoration the reset submonoid `resetSubmonoid` acting on $Q$ by evaluation,
--   base $G$ acting on itself by left multiplication — every $\mathrm{act}(g) \in \mathrm{End}(Q)$,
--   $g \in G$, is covered (`Covers`) with respect to the decoding `groupProj`. (DKS Lemma 2.9,
--   appendix, cover $(k_1, g)$.)
--
--   *Proof sketch.* Take $\hat{w} := (\lambda m.\,1,\ g)$ (trivial decoration, base $g$). Then
--   $\hat{w} \bullet (q, m) = (q, g m)$ and $\varphi = \mathrm{act}(gm)(q) =
--   \mathrm{act}(g)(\mathrm{act}(m)(q)) = \mathrm{act}(g)(\varphi(q,m))$ by multiplicativity. Direct
--   computation.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L729-L737
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L729-L737

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

theorem KrohnRhodes.cover_act_group {G Q : Type} [Group G] (act : G →* Function.End Q) (g : G) :
    ∃ w : WreathProduct ↥(resetSubmonoid Q) G G,
      Covers (groupProj act) w (act g) := by sorry
