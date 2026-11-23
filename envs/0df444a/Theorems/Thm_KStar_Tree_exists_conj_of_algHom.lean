-- Prove2me | Theorems.Thm_KStar_Tree_exists_conj_of_algHom
-- name    : KStar.Tree.exists_conj_of_algHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:46.297336+00:00
-- url     : https://prove2.me/theorems/6d4a029d-4dd0-46ac-9474-52092621f167
-- title:
--   Tree: exists conj of alg Hom
-- statement:
--   The Tree construction uses the exists conj of alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/SkolemNoether.lean#L5-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/SkolemNoether.lean#L5-L124

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_SkolemNoether
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree

theorem KStar.Tree.exists_conj_of_algHom {B : Type} [CommRing B] [IsLocalRing B] {r : ℕ}
    (θ : Matrix (Fin r) (Fin r) B →ₐ[B] Matrix (Fin r) (Fin r) B) :
    ∃ J : GL (Fin r) B, ∀ x, θ x * (J : Matrix (Fin r) (Fin r) B) = (J : Matrix (Fin r) (Fin r) B) * x := by sorry
