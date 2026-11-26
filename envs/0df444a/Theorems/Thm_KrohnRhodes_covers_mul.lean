-- Prove2me | Theorems.Thm_KrohnRhodes_covers_mul
-- name    : KrohnRhodes.covers_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:06.813775+00:00
-- url     : https://prove2.me/theorems/68a98d39-35c1-5e4d-8aea-229110c19423
-- title:
--   Krohn Rhodes: covers mul
-- statement:
--   **Covers compose: a product of covers covers the product.** In the setting of `Covers`: if
--   $w_1$ covers $t_1$ and $w_2$ covers $t_2$, then $w_1 w_2$ covers $t_1 t_2$ (composition in
--   $\mathrm{End}(R)$, i.e. $(t_1 t_2)(r) = t_1(t_2(r))$). This is the step in the proof of DKS
--   Prop 2.3(1); with left actions
--   the orders align without reversal.
--
--   *Proof sketch.* $\varphi((w_1 w_2) \bullet s) = \varphi(w_1 \bullet (w_2 \bullet s))$ by the
--   wreath action law ($(w_1 w_2) \bullet s = w_1 \bullet (w_2 \bullet s)$, computed from
--   `WreathProduct.mul_func`/`mul_base` and the action laws `mul_smul` of $A$ on $P$ and of $B$ on
--   $X$);
--   this equals $t_1(\varphi(w_2 \bullet s)) = t_1(t_2(\varphi(s)))$ by the two cover hypotheses.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L228-L238
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L228-L238

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

theorem KrohnRhodes.covers_mul {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P] [MulAction B X]
    (φ : P × X → R) {w₁ w₂ : WreathProduct A B X} {t₁ t₂ : Function.End R}
    (h₁ : Covers φ w₁ t₁) (h₂ : Covers φ w₂ t₂) :
    Covers φ (w₁ * w₂) (t₁ * t₂) := by sorry
