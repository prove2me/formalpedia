-- Prove2me | Theorems.Thm_KrohnRhodes_dks_proj_surjective
-- name    : KrohnRhodes.dks_proj_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:12.185908+00:00
-- url     : https://prove2.me/theorems/e134908e-f1a1-5790-81d0-8042729c0ee4
-- title:
--   Krohn Rhodes: dks proj surjective
-- statement:
--   **The decoding map is surjective.** If $Q$ is nonempty, the decoding map `dksProj` is
--   surjective: every $q \in Q$ is $\varphi(p_0, \mathrm{inl}\,q)$ for any point $p_0$ of the image
--   state set $cQ$ — which is nonempty because $\mathrm{act}(c)(q_0) \in cQ$ for any $q_0 \in Q$.
--   (The empty/subsingleton $Q$ case never reaches this lemma: the induction `dks_aux` dispatches it
--   to the empty tower first.)
--
--   *Proof sketch.* As stated: $cQ$ is inhabited by $\langle \mathrm{act}(c)(q_0), q_0 \rangle$ for
--   $q_0$ from `Nonempty` $Q$, and $\varphi(p_0, \mathrm{inl}\,q) = q$.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L550-L555
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L550-L555

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

theorem KrohnRhodes.dks_proj_surjective {M Q : Type} [Monoid M] [Nonempty Q]
    (act : M →* Function.End Q) (c : M) (N : Submonoid M) :
    Function.Surjective (dksProj act c N) := by sorry
