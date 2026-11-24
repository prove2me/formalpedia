-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_dualData_transfer
-- name    : GlobalTheory.CompanionTheory.PTIso.ShaTransfer.dualData_transfer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:48.106261+00:00
-- url     : https://prove2.me/theorems/bd950bd0-7871-49a6-bb76-c8e1a5ec7d79
-- title:
--   Sha Transfer: dual Data transfer
-- statement:
--   The Sha Transfer construction uses the dual Data transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichTransport.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichTransport.lean#L24-L33

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.ShaTransfer

theorem GlobalTheory.CompanionTheory.PTIso.ShaTransfer.dualData_transfer {R A B A' B' : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B)
    (h : Finite A' ∧ Finite B' ∧ Nonempty (B' ≃ₗ[R] Module.Dual R A') ∧
      Nat.card A' = Nat.card B') :
    Finite A ∧ Finite B ∧ Nonempty (B ≃ₗ[R] Module.Dual R A) ∧ Nat.card A = Nat.card B := by sorry
