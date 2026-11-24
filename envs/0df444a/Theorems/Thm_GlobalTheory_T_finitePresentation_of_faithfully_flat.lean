-- Prove2me | Theorems.Thm_GlobalTheory_T_finitePresentation_of_faithfully_flat
-- name    : GlobalTheory.T.finitePresentation_of_faithfully_flat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:37.871746+00:00
-- url     : https://prove2.me/theorems/3cd75f56-d68d-49c2-9689-5ef92493047c
-- title:
--   T: finite Presentation of faithfully flat
-- statement:
--   The T construction uses the finite Presentation of faithfully flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlatStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlatStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finitePresentation_of_faithfully_flat : ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D → Module.FaithfullyFlat C D → Algebra.FinitePresentation R D → Algebra.FinitePresentation R C := by sorry
