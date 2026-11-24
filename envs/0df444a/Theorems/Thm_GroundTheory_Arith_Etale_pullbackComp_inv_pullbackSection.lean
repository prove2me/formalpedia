-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_pullbackComp_inv_pullbackSection
-- name    : GroundTheory.Arith.Etale.pullbackComp_inv_pullbackSection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:35.869846+00:00
-- url     : https://prove2.me/theorems/e8a0d6c2-dda8-4e05-b0b0-b2fa1034b988
-- title:
--   Etale: pullback Comp inv pullback Section
-- statement:
--   The Etale construction uses the pullback Comp inv pullback Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ModulesPullback.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ModulesPullback.lean#L29-L39

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {T U W : Scheme.{u}}

theorem GroundTheory.Arith.Etale.pullbackComp_inv_pullbackSection (f : W ⟶ T) (g : T ⟶ U) (N : U.Modules) (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app ⊤ (pullbackSection (f ≫ g) N n) =
      pullbackSection f _ (pullbackSection g N n) := by sorry
