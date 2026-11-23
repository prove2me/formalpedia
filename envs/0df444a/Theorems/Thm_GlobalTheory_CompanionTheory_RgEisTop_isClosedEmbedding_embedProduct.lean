-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_isClosedEmbedding_embedProduct
-- name    : GlobalTheory.CompanionTheory.RgEisTop.isClosedEmbedding_embedProduct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:08.681187+00:00
-- url     : https://prove2.me/theorems/2a819944-c366-49aa-b110-b68a1bcb0f00
-- title:
--   Rg Eis Top: is Closed Embedding embed Product
-- statement:
--   The Rg Eis Top construction uses the is Closed Embedding embed Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L12-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTop
variable {M : Type} [TopologicalSpace M] [Monoid M] [ContinuousMul M] [T2Space M]

theorem GlobalTheory.CompanionTheory.RgEisTop.isClosedEmbedding_embedProduct : IsClosedEmbedding (Units.embedProduct M) := by sorry
