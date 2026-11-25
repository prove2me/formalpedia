-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
-- name    : GroundTheory.Arith.Etale.pullbackUnitApp_comp_hom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:04.046144+00:00
-- url     : https://prove2.me/theorems/f9395119-760b-463e-b693-7e3783884d83
-- title:
--   Etale: pullback Unit App comp hom
-- statement:
--   The Etale construction uses the pullback Unit App comp hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohZariski.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohZariski.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
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
variable {V T U : Scheme.{u}}

theorem GroundTheory.Arith.Etale.pullbackUnitApp_comp_hom (f : V ⟶ T) (g : T ⟶ U) (N : U.Modules) (O : U.Opens)
    (n : Γ(N, O)) :
    ((Scheme.Modules.pullbackComp f g).hom.app N).app ((f ≫ g) ⁻¹ᵁ O)
      (pullbackUnitApp f _ (g ⁻¹ᵁ O) (pullbackUnitApp g N O n)) =
        pullbackUnitApp (f ≫ g) N O n := by sorry
