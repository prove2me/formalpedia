-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_scale_eq_prod
-- name    : GroundTheory.PAdicHodge.map_scale_eq_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:54.878784+00:00
-- url     : https://prove2.me/theorems/f795c981-aa6f-462e-bc8e-ddeae0734a7b
-- title:
--   PAdic Hodge: map scale eq prod
-- statement:
--   The PAdic Hodge construction uses the map scale eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L252-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L252-L278

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]

theorem GroundTheory.PAdicHodge.map_scale_eq_prod {Q : F[X]} (hQ : Q.Monic) (β c : F) (hc : c ≠ 0) :
    (Polynomial.C (c⁻¹ ^ Q.natDegree) * Q.comp (Polynomial.C β + Polynomial.C c * X)).map
        (algebraMap F E) =
      ((Q.map (algebraMap F E)).roots.map fun γ =>
        X - Polynomial.C ((γ - algebraMap F E β) / algebraMap F E c)).prod := by sorry
