-- Prove2me | Theorems.Thm_JuschenkoMonod_countable_fullGroup_and_mulEquiv_iff_flipConj
-- name    : JuschenkoMonod.countable_fullGroup_and_mulEquiv_iff_flipConj
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:31:57.916608+00:00
-- url     : https://prove2.me/theorems/cedf2571-5efc-40e6-83fb-477ecf10204e
-- title:
--   p. 775 — [[T]] is countable, and for minimal systems a complete invariant of flip-conjugacy (Giordano–Putnam–Skau, Corollary 4.4)
-- statement:
--   Let $T_1$ and $T_2$ be homeomorphisms of Cantor spaces $C_1$ and $C_2$. Then $[[T_1]]$ is countable. If moreover $T_1$ and $T_2$ are minimal, then $[[T_1]]$ and $[[T_2]]$ are isomorphic groups if and only if there is a homeomorphism $h\colon C_1 \to C_2$ with $h \circ T_1 = T_2 \circ h$ or $h \circ T_1 = T_2^{-1} \circ h$.
--
--   *Formalization note.* The sentence speaks of any Cantor system $(T, C)$; the cited Corollary 4.4 of Giordano–Putnam–Skau is a theorem about Cantor minimal systems, and the complete-invariant part is stated for minimal systems.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 775, the Giordano–Putnam–Skau classification, which cites Giordano, T., Putnam, I. F. and Skau, C. F., Full groups of Cantor minimal systems, Israel J. Math. 111 (1999) 285–320, https://doi.org/10.1007/BF02810689, Corollary 4.4

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem countable_fullGroup_and_mulEquiv_iff_flipConj (C₁ C₂ : Type*) [TopologicalSpace C₁]
    [TopologicalSpace C₂] (hC₁ : CantorSystems.IsCantorSpace C₁)
    (hC₂ : CantorSystems.IsCantorSpace C₂) (T₁ : C₁ ≃ₜ C₁) (T₂ : C₂ ≃ₜ C₂) :
    Countable (fullGroup T₁) ∧
      (IsMinimal T₁ → IsMinimal T₂ →
        (Nonempty (fullGroup T₁ ≃* fullGroup T₂) ↔
          ∃ h : C₁ ≃ₜ C₂, (∀ x, h (T₁ x) = T₂ (h x)) ∨ ∀ x, h (T₁ x) = T₂.symm (h x))) := by
  sorry

end JuschenkoMonod
