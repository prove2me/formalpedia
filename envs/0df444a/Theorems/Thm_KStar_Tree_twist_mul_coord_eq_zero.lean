-- Prove2me | Theorems.Thm_KStar_Tree_twist_mul_coord_eq_zero
-- name    : KStar.Tree.twist_mul_coord_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:40.688646+00:00
-- url     : https://prove2.me/theorems/3dd13b22-8c8b-4ea3-8c21-eff48dbed499
-- title:
--   Tree: twist mul coord eq zero
-- statement:
--   The Tree construction uses the twist mul coord eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/PolarTraceMulVecMulVecEq.lean#L28-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/PolarTraceMulVecMulVecEq.lean#L28-L89

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TwistTrace
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_PolarTraceMulVecMulVecEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
open Matrix

theorem KStar.Tree.twist_mul_coord_eq_zero : ∀ (Γ A : Type) [Group Γ] [CommRing A] [IsLocalRing A] (r : ℕ) (T T' : Γ →* Matrix (Fin r) (Fin r) A) (χ : Γ →* A) (c : Γ →* Γ) (J : GL (Fin r) A) (L : Subgroup Γ) (z : Γ) (d : Aˣ) (x y : Γ → Fin r → A), Submodule.span A (Set.range T) = ⊤ → (∀ g, T' (c g) = (J : Matrix (Fin r) (Fin r) A) * (χ g • T g) * ((J⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)) → L.Normal → (∀ h ∈ L, c h ∈ L) → (∀ h ∈ L, T h = 1 ∧ T' h = 1) → T z = (d : A) • 1 → T' z = ((d⁻¹ : Aˣ) : A) • 1 → T (c z) = ((d⁻¹ : Aˣ) : A) • 1 → T' (c z) = (d : A) • 1 → IsUnit ((d : A) ^ 2 - 1) → (∀ g h, x (g * h) = x g + (T g).mulVec (x h)) → (∀ g h, y (g * h) = y g + (T' g).mulVec (y h)) → (∀ h ∈ L, x h ⬝ᵥ y h = x (c h) ⬝ᵥ y (c h)) → ∀ g₀ : Γ, ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (χ g₀ ^ r - 1) * x h a * y h' b = 0 := by sorry
