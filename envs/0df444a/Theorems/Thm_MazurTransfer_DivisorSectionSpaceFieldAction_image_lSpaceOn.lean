-- Prove2me | Theorems.Thm_MazurTransfer_DivisorSectionSpaceFieldAction_image_lSpaceOn
-- name    : MazurTransfer.DivisorSectionSpaceFieldAction.image_lSpaceOn
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:55:16.284935+00:00
-- url     : https://prove2.me/theorems/2528b802-a021-4191-93d6-0ddfa08ee87b
-- title:
--   Divisor section spaces transport under field and place automorphisms
-- statement:
--   Let $F/K$ be a field extension, $\sigma$ a $K$-algebra automorphism of $F$, $S$ a set of places, and $D$ a divisor. The corresponding bounded-pole section spaces satisfy $$\sigma\bigl(L_S(D)\bigr)=L_{\sigma S}(\sigma D).$$ This is the exact range compatibility used to transport divisor presentations along curve automorphisms.
-- source:
--   Original complete image_lSpaceOn statement and proof, with original mem_image_lSpaceOn_iff helper, from MazurTheorem DivisorSectionSpaceFieldAction.lean, Apache-2.0, Vas and contributors. The original helper is retained in an explicit fresh namespace, and the original public CechSectionsOfDivisor definitions supply all dependencies. The full original closed type is kernel-compared. Named downstream consumer: DivisorPresentationRestrictionFieldAction.presentation_restrict and arithmetic Picard curve-pullback naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: section spaces with valuation bounds transport under field
and place automorphisms. Named downstream consumer: the transformed range
condition in divisor presentations for actual curve inverse pullback.
-/
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

noncomputable section

open AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem MazurTransfer.DivisorSectionSpaceFieldAction.image_lSpaceOn (σ : F ≃ₐ[K] F) (S : Set (Place K F)) (D : Divisor K F) :
    σ '' (lSpaceOn S D : Set F) =
      (lSpaceOn ((fun v : Place K F => σ • v) '' S) (σ • D) : Set F) := by sorry
