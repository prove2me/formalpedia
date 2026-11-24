-- Prove2me | Theorems.Thm_GlobalTheory_T_totally_complex_of_ring_equiv
-- name    : GlobalTheory.T.totally_complex_of_ring_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:51.132848+00:00
-- url     : https://prove2.me/theorems/a43a605b-1245-4021-8555-3a8b9391347c
-- title:
--   T: totally complex of ring equiv
-- statement:
--   The T construction uses the totally complex of ring equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TotallyComplexOfRingEquivStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TotallyComplexOfRingEquivStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TotallyComplexOfRingEquiv
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TotallyComplexOfRingEquivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.totally_complex_of_ring_equiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by sorry
