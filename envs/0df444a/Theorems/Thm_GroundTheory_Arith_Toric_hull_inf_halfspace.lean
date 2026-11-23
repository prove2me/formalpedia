-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_hull_inf_halfspace
-- name    : GroundTheory.Arith.Toric.hull_inf_halfspace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:33.117748+00:00
-- url     : https://prove2.me/theorems/57811fd1-d966-4921-a39d-10d405a520f6
-- title:
--   Toric: hull inf halfspace
-- statement:
--   The Toric construction uses the hull inf halfspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L123-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean#L123-L182

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

theorem GroundTheory.Arith.Toric.hull_inf_halfspace (S : Finset V) (g : Dual 𝕜 V) [DecidableEq V] :
    hull 𝕜 (S : Set V) ⊓ (positive 𝕜 𝕜).comap g =
      hull 𝕜 ((S.filter (fun s => 0 ≤ g s) ∪
        ((S ×ˢ S).filter (fun st => 0 < g st.1 ∧ g st.2 < 0)).image
          (fun st => g st.1 • st.2 - g st.2 • st.1) : Finset V) : Set V) := by sorry
