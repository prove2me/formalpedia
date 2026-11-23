-- Prove2me | Theorems.Thm_GlobalTheory_Unif_locallyQuasiFinite_of_isPullback_surjective
-- name    : GlobalTheory.Unif.locallyQuasiFinite_of_isPullback_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:36.276577+00:00
-- url     : https://prove2.me/theorems/75dfd589-ec79-47e2-9caa-3ea8e8fe8dae
-- title:
--   Unif: locally Quasi Finite of is Pullback surjective
-- statement:
--   The Unif construction uses the locally Quasi Finite of is Pullback surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocallyQuasiFiniteOfIsPullbackSurjective.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocallyQuasiFiniteOfIsPullbackSurjective.lean#L7-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyQuasiFiniteOfIsPullbackSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.Unif

theorem GlobalTheory.Unif.locallyQuasiFinite_of_isPullback_surjective :
    ∀ (X Z X' Z' : Scheme.{0}) (φ : X ⟶ Z) (φ' : X' ⟶ Z') (a : X' ⟶ X) (p : Z' ⟶ Z),
      IsPullback a φ' φ p → Surjective p → LocallyOfFiniteType φ → QuasiCompact φ →
      LocallyQuasiFinite φ' → LocallyQuasiFinite φ := by sorry
