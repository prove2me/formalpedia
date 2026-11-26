-- Prove2me | Theorems.Thm_KrohnRhodes_cover_act_c
-- name    : KrohnRhodes.cover_act_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:28.701696+00:00
-- url     : https://prove2.me/theorems/42e2deb2-f815-56dc-a4a5-0ba23d0afb11
-- title:
--   Krohn Rhodes: cover act c
-- statement:
--   **Cover family 3: the action of the chosen non-unit is covered.** In the wreath product of
--   `cover_const_end`, the transformation $\mathrm{act}(c) \in \mathrm{End}(Q)$ itself is covered
--   (`Covers`) with respect to the decoding `dksProj`. This is THE local-divisor step of DKS Thm 3.1
--   (their decoration $f_c$ with $y f_c = \overline{y \cdot c}$ on states and $n f_c = cnc$ on $N$,
--   base constant onto $1 \in N$).
--
--   *Proof sketch.* Take $\hat{w} := (f_c,\ \overline{\mathrm{inr}\,1})$ with decoration
--   $f_c(\mathrm{inl}\,q) := \overline{\langle \mathrm{act}(c)(q) \rangle}$ (a constant of
--   $\mathrm{End}(cQ)$, hence in the decoration closure) and
--   $f_c(\mathrm{inr}\,n) := \mathrm{localActHom}\,\langle c n c \rangle$ (in the range of the local
--   action, hence in the decoration closure; $cnc \in cM \cap Mc$ with the two evident factorizations
--   $cnc = c \cdot (nc) = (cn) \cdot c$). Then
--   $\hat{w} \bullet (p, y) = (f_c(y) \bullet p,\ \mathrm{inr}\,1)$, so
--   $\varphi(\hat{w} \bullet (p,y)) = \mathrm{act}(1)$ applied to the underlying value of
--   $f_c(y) \bullet p$ — which is that value itself. For $y = \mathrm{inl}\,q$: the value is
--   $\mathrm{act}(c)(q) = \mathrm{act}(c)(\varphi(p, \mathrm{inl}\,q))$. For $y = \mathrm{inr}\,n$
--   and $p = \mathrm{act}(c)(x)$: writing $cnc = b'c$ for the chosen right factorization baked into
--   `localActHom`, the value is $\mathrm{act}(b')(p) = \mathrm{act}(b'c)(x) = \mathrm{act}(cnc)(x) =
--   \mathrm{act}(c)(\mathrm{act}(n)(\mathrm{act}(c)(x))) = \mathrm{act}(c)(\varphi(p,
--   \mathrm{inr}\,n))$ — the chosen $b'$ drops out because the displayed value $\mathrm{act}(cnc)(x)$
--   is determined by $cnc$ alone. Direct computation.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L626-L666
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L626-L666

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

theorem KrohnRhodes.cover_act_c {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (N : Submonoid M) :
    ∃ w : WreathProduct ↥(closureMonoid (localActHom act c))
      ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N),
      Covers (dksProj act c N) w (act c) := by sorry
