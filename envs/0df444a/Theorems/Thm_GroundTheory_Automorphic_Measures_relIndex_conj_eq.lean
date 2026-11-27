-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_relIndex_conj_eq
-- name    : GroundTheory.Automorphic.Measures.relIndex_conj_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:28.726217+00:00
-- url     : https://prove2.me/theorems/cc140045-3c49-58b2-846d-343ba58b7925
-- title:
--   Measures: rel Index conj eq
-- statement:
--   The Measures construction uses the rel Index conj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L215-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L215-L229

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem GroundTheory.Automorphic.Measures.relIndex_conj_eq {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hKc : IsCompact (K : Set (GL (Fin n) F))) (g : GL (Fin n) F) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      (K.map (MulAut.conj g⁻¹).toMonoidHom).relIndex K := by sorry
