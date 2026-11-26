-- Prove2me | Theorems.Thm_KrohnRhodes_cover_const_end
-- name    : KrohnRhodes.cover_const_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:22.170151+00:00
-- url     : https://prove2.me/theorems/57be994f-2d2f-5ded-b99a-4a21a0f7bc0b
-- title:
--   Krohn Rhodes: cover const end
-- statement:
--   **Cover family 1: constants are covered.** In the wreath product
--   $\overline{(cQ, M_c)} \wr_{Q \sqcup N} \overline{(Q \sqcup N, N)}$ — decoration the constants
--   closure `closureMonoid` of the local action `localActHom`, base the constants closure of the
--   extension action `extAct`, both acting by evaluation — every constant transformation
--   $\overline{x} \in \mathrm{End}(Q)$, $x \in Q$, is covered (`Covers`) with respect to the decoding
--   `dksProj`. (DKS Thm 3.1, first cover family.)
--
--   *Proof sketch.* Take $\hat{w} := (\lambda y.\,1,\ \overline{\mathrm{inl}\,x})$ — trivial
--   decoration, base the constant onto $\mathrm{inl}\,x$, which lies in the base closure because
--   constants are generators. Then $\hat{w} \bullet (p, y) = (p, \mathrm{inl}\,x)$, so
--   $\varphi(\hat{w} \bullet (p,y)) = x = \overline{x}(\varphi(p,y))$. Direct computation.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L568-L576
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L568-L576

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

theorem KrohnRhodes.cover_const_end {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (N : Submonoid M) (x : Q) :
    ∃ w : WreathProduct ↥(closureMonoid (localActHom act c))
      ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N),
      Covers (dksProj act c N) w (constEnd x) := by sorry
