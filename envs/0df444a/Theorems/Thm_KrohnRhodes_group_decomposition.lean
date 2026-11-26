-- Prove2me | Theorems.Thm_KrohnRhodes_group_decomposition
-- name    : KrohnRhodes.group_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:35.635668+00:00
-- url     : https://prove2.me/theorems/ae3ec433-ba64-5193-bd7f-71748a73eb63
-- title:
--   Krohn Rhodes: group decomposition
-- statement:
--   **Group case: the closure of a group representation divides resets wreath G.** Let $G$ be a
--   group and $\mathrm{act} \colon G \to^* \mathrm{End}(Q)$ a monoid homomorphism (no faithfulness
--   needed). Then the constants closure $\overline{(Q, G)}$ (`closureMonoid`) divides, as a
--   semigroup, the wreath product $U(Q) \wr_G G$ of `cover_act_group` (reset decoration over the left
--   regular base). This is a monoid-level form of DKS Lemma 2.9.
--
--   *Proof sketch.* Apply `sgdiv_of_covering` with the decoding `groupProj`, surjective because
--   $\varphi(q, 1) = \mathrm{act}(1)(q) = q$, and the DEFINING generating set
--   $\mathrm{range}(\mathrm{act}) \cup \{\overline{x}\}$ of the closure (`closureMonoid` is literally
--   the closure of this set, so the generation hypothesis is definitional and no generating-set
--   transport is needed). Coverage: $\mathrm{act}(g)$ by `cover_act_group`; constants by
--   `cover_const_group`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L779-L794
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L779-L794

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

theorem KrohnRhodes.group_decomposition {G Q : Type} [Group G] (act : G →* Function.End Q) :
    SgDiv ↥(closureMonoid act) (WreathProduct ↥(resetSubmonoid Q) G G) := by sorry
