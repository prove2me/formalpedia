-- Prove2me | Theorems.Thm_KrohnRhodes_cover_act_of_mem
-- name    : KrohnRhodes.cover_act_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:10.096729+00:00
-- url     : https://prove2.me/theorems/c0a72bd8-db15-4be0-ab66-d2f4a1f32c41
-- title:
--   Krohn Rhodes: cover act of mem
-- statement:
--   **Cover family 2: the action of a submonoid element is covered.** In the wreath product of
--   `cover_const_end`, for every $n \in N$ the transformation $\mathrm{act}(n) \in \mathrm{End}(Q)$
--   is covered (`Covers`) with respect to the decoding `dksProj`. (DKS Thm 3.1, second cover family —
--   their $k_c$ with identity decoration.)
--
--   *Proof sketch.* Take $\hat{w} := (\lambda y.\,1,\ \mathrm{extAct}(n))$ — trivial decoration, base
--   the extension action of $n$ (a generator of the base closure). On $(p, \mathrm{inl}\,q)$:
--   $\hat{w} \bullet (p, \mathrm{inl}\,q) = (p, \mathrm{inl}\,(\mathrm{act}(n)(q)))$, and
--   $\varphi = \mathrm{act}(n)(q) = \mathrm{act}(n)(\varphi(p, \mathrm{inl}\,q))$. On
--   $(p, \mathrm{inr}\,m)$: $\hat{w} \bullet (p, \mathrm{inr}\,m) = (p, \mathrm{inr}\,(n m))$, and
--   $\varphi = \mathrm{act}(nm)(p) = \mathrm{act}(n)(\mathrm{act}(m)(p)) = \mathrm{act}(n)(\varphi(p,
--   \mathrm{inr}\,m))$ by multiplicativity. Direct computation.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L590-L603
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L590-L603

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

theorem KrohnRhodes.cover_act_of_mem {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (N : Submonoid M) (n : ↥N) :
    ∃ w : WreathProduct ↥(closureMonoid (localActHom act c))
      ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N),
      Covers (dksProj act c N) w (act n.1) := by sorry
