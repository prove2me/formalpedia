-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_nine_ladder
-- name    : GlobalTheory.CompanionTheory.PTIso.NineTransfer.nine_ladder
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:04.393042+00:00
-- url     : https://prove2.me/theorems/b7d54839-9d73-489b-b39e-bc805e06dc45
-- title:
--   Nine Transfer: nine ladder
-- statement:
--   The Nine Transfer construction uses the nine ladder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L34-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L34-L81

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.NineTransfer
variable {R : Type*} [CommRing R]

theorem GlobalTheory.CompanionTheory.PTIso.NineTransfer.nine_ladder {X0 X1 X2 Y0 Y1 Y2 W0 W1 W2 X0' X1' X2' Y0' Y1' Y2' W0' W1' W2' : Type*}
    [AddCommGroup X0] [Module R X0] [AddCommGroup X1] [Module R X1]
    [AddCommGroup X2] [Module R X2] [AddCommGroup Y0] [Module R Y0]
    [AddCommGroup Y1] [Module R Y1] [AddCommGroup Y2] [Module R Y2]
    [AddCommGroup W0] [Module R W0] [AddCommGroup W1] [Module R W1]
    [AddCommGroup W2] [Module R W2]
    [AddCommGroup X0'] [Module R X0'] [AddCommGroup X1'] [Module R X1']
    [AddCommGroup X2'] [Module R X2'] [AddCommGroup Y0'] [Module R Y0']
    [AddCommGroup Y1'] [Module R Y1'] [AddCommGroup Y2'] [Module R Y2']
    [AddCommGroup W0'] [Module R W0'] [AddCommGroup W1'] [Module R W1']
    [AddCommGroup W2'] [Module R W2']
    (a0 : X0' ≃ₗ[R] X0) (a1 : X1' ≃ₗ[R] X1) (a2 : X2' ≃ₗ[R] X2)
    (p0 : Y0' ≃ₗ[R] Y0) (p1 : Y1' ≃ₗ[R] Y1) (p2 : Y2' ≃ₗ[R] Y2)
    (w0 : W0' ≃ₗ[R] W0) (w1 : W1' ≃ₗ[R] W1) (w2 : W2' ≃ₗ[R] W2)
    {g0 : X0 →ₗ[R] Y0} {g1 : X1 →ₗ[R] Y1} {g2 : X2 →ₗ[R] Y2}
    {t0 : Y0 →ₗ[R] W0} {t1 : Y1 →ₗ[R] W1} {t2 : Y2 →ₗ[R] W2}
    {g0' : X0' →ₗ[R] Y0'} {g1' : X1' →ₗ[R] Y1'} {g2' : X2' →ₗ[R] Y2'}
    {t0' : Y0' →ₗ[R] W0'} {t1' : Y1' →ₗ[R] W1'} {t2' : Y2' →ₗ[R] W2'}
    (hg0 : ∀ x, g0 (a0 x) = p0 (g0' x)) (hg1 : ∀ x, g1 (a1 x) = p1 (g1' x))
    (hg2 : ∀ x, g2 (a2 x) = p2 (g2' x))
    (ht0 : ∀ y, t0 (p0 y) = w0 (t0' y)) (ht1 : ∀ y, t1 (p1 y) = w1 (t1' y))
    (ht2 : ∀ y, t2 (p2 y) = w2 (t2' y))
    (h : ∃ (d1' : W0' →ₗ[R] X1') (d2' : W1' →ₗ[R] X2'),
      Function.Injective g0' ∧ Function.Exact g0' t0' ∧ Function.Exact t0' d1' ∧
      Function.Exact d1' g1' ∧ Function.Exact g1' t1' ∧ Function.Exact t1' d2' ∧
      Function.Exact d2' g2' ∧ Function.Exact g2' t2' ∧ Function.Surjective t2') :
    ∃ (d1 : W0 →ₗ[R] X1) (d2 : W1 →ₗ[R] X2),
      Function.Injective g0 ∧ Function.Exact g0 t0 ∧ Function.Exact t0 d1 ∧
      Function.Exact d1 g1 ∧ Function.Exact g1 t1 ∧ Function.Exact t1 d2 ∧
      Function.Exact d2 g2 ∧ Function.Exact g2 t2 ∧ Function.Surjective t2 := by sorry
