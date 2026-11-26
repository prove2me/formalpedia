-- Prove2me | Theorems.Thm_KrohnRhodes_local_act_injective
-- name    : KrohnRhodes.local_act_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:14.7238+00:00
-- url     : https://prove2.me/theorems/9acb2fba-af78-56ea-a8a2-1368c7a7238a
-- title:
--   Krohn Rhodes: local act injective
-- statement:
--   **The local divisor acts faithfully on the image state set.** If
--   $\mathrm{act} \colon M \to^* \mathrm{End}(Q)$ is injective, then the local-divisor action
--   `localActHom` is injective: distinct elements of $M_c$ induce distinct transformations of $cQ$.
--   This is DKS Lemma 2.11, supplying the injectivity hypothesis when the
--   induction `dks_aux` recurses into $(cQ, M_c)$.
--
--   *Proof sketch.* Suppose $u, v \in M_c$ act identically on $cQ$. For every $x \in Q$ the point
--   $\mathrm{act}(c)(x)$ lies in $cQ$, and the displayed well-definedness formula of `localActHom`
--   gives $\mathrm{act}(u)(x) = u \bullet (\mathrm{act}(c)(x)) = v \bullet (\mathrm{act}(c)(x)) =
--   \mathrm{act}(v)(x)$ (values through `LocalDivisor.val`); hence
--   $\mathrm{act}(u.\mathrm{val}) = \mathrm{act}(v.\mathrm{val})$ as transformations, so
--   $u.\mathrm{val} = v.\mathrm{val}$ by injectivity of $\mathrm{act}$, so $u = v$
--   (`LocalDivisor.ext`).
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L457-L474
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L457-L474

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

theorem KrohnRhodes.local_act_injective {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (hf : Function.Injective act) : Function.Injective (localActHom act c) := by sorry
