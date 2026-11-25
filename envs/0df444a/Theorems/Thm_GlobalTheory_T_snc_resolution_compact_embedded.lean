-- Prove2me | Theorems.Thm_GlobalTheory_T_snc_resolution_compact_embedded
-- name    : GlobalTheory.T.snc_resolution_compact_embedded
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:47:38.742945+00:00
-- url     : https://prove2.me/theorems/43469d8b-6cad-5689-a192-1caa8663cbc4
-- title:
--   T: snc resolution compact embedded
-- statement:
--   The T construction uses the snc resolution compact embedded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbeddedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionCompactEmbeddedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbeddedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.snc_resolution_compact_embedded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → CompactSpace (SncRes.Pts P) ∧ ∀ p : (k : K) → ι k, IsOpen (SncRes.src P p) ∧ Topology.IsEmbedding (fun x : SncRes.src P p => SncRes.coord P p x) := by sorry
