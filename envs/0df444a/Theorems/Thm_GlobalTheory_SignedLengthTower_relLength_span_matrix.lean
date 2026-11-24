-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthTower_relLength_span_matrix
-- name    : GlobalTheory.SignedLengthTower.relLength_span_matrix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:12:37.940312+00:00
-- url     : https://prove2.me/theorems/425b154b-d47b-4e56-9904-206a09ca5c3f
-- title:
--   Signed Length Tower: rel Length span matrix
-- statement:
--   The Signed Length Tower construction uses the rel Length span matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanMatrix.lean#L70-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanMatrix.lean#L70-L95

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthTower

theorem GlobalTheory.SignedLengthTower.relLength_span_matrix {R V ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι] {a c : ι → V}
    (ha : LinearIndependent R a) (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, M i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range c)) =
      Ring.ord R M.det := by sorry
