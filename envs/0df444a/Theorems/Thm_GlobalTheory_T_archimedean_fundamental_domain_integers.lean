-- Prove2me | Theorems.Thm_GlobalTheory_T_archimedean_fundamental_domain_integers
-- name    : GlobalTheory.T.archimedean_fundamental_domain_integers
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:54.694821+00:00
-- url     : https://prove2.me/theorems/d5b6796e-091f-454f-972a-e881b5019e9d
-- title:
--   T: archimedean fundamental domain integers
-- statement:
--   The T construction uses the archimedean fundamental domain integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanFundamentalDomainIntegersStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanFundamentalDomainIntegersStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.archimedean_fundamental_domain_integers : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧ li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by sorry
