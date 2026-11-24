-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_lift_datumHat
-- name    : GlobalTheory.LastSteps.lift_datumHat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:13.266818+00:00
-- url     : https://prove2.me/theorems/08020b2e-614d-401b-83bd-1b82da85b04e
-- title:
--   Last Steps: lift datum Hat
-- statement:
--   The Last Steps construction uses the lift datum Hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L501-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L501-L510

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n] [Fintype n'] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
  (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
  [Module ℂ A] (x' : Matrix n'' n k) (η : n → k)
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
variable [DecidableEq n'] {L : Submodule 𝒪[k] (n' → k)} [L.IsLattice k] {φ : Form k n' M}

theorem GlobalTheory.LastSteps.lift_datumHat {π : Representation ℂ (GL n' k) M} {θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A}
    (hφ : φ ∈ Mram k n' M) (he : φ ∈ EqForm π) (hθ : IsLiftInv π θ L) {P P' : Pair k n'} (hP : P.ker = L)
    (hP' : P'.lat = L) :
    latInd LY L'' x' • θ (φ P) (fun x₀ => datumHat ψ ε μ q P LY x₀ η) =
      (volQ μ q LY : ℂ) • ∑ Q ∈ withLat LY, phiOne Q (lastPair q L'') (withRow x' η) •
        θ (dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') (phiOne P' Q) := by sorry
