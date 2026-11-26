-- Prove2me | Theorems.Thm_KrohnRhodes_covers_unique
-- name    : KrohnRhodes.covers_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:02.735886+00:00
-- url     : https://prove2.me/theorems/4f2b87c7-409f-5979-8420-eb00ec04d04e
-- title:
--   Krohn Rhodes: covers unique
-- statement:
--   **A wreath element covers at most one transformation (surjective decoding).** In the setting
--   of `Covers`, assume $\varphi$ is surjective. If $w$ covers both $t_1$ and $t_2$, then $t_1 = t_2$
--   (the injectivity argument in the proof of DKS Prop 2.3(2)). This is what makes the decoded
--   transformation of a covering wreath element well-defined in `sgdiv_of_covering`.
--
--   *Proof sketch.* For every $r \in R$ pick $s$ with $\varphi(s) = r$ (surjectivity); then
--   $t_1(r) = \varphi(w \bullet s) = t_2(r)$, and transformations agreeing pointwise are equal
--   (`funext`).
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L248-L254
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L248-L254

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

theorem KrohnRhodes.covers_unique {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P] [MulAction B X]
    {φ : P × X → R} (hφ : Function.Surjective φ) {w : WreathProduct A B X}
    {t₁ t₂ : Function.End R} (h₁ : Covers φ w t₁) (h₂ : Covers φ w t₂) :
    t₁ = t₂ := by sorry
