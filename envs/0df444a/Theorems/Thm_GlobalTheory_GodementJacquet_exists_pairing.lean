-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_exists_pairing
-- name    : GlobalTheory.GodementJacquet.exists_pairing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:14.730561+00:00
-- url     : https://prove2.me/theorems/c6835a7a-b06c-43b5-93cd-4224b35723ab
-- title:
--   Godement Jacquet: exists pairing
-- statement:
--   The Godement Jacquet construction uses the exists pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairDetTwist.lean#L530-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairDetTwist.lean#L530-L568

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel GlobalTheory.RootEx
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
local notation "e₀" => stdSum (rfl : _ + _ = _ + _)
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsMulRightInvariant] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)

theorem GlobalTheory.GodementJacquet.exists_pairing (hμ : IsSmoothChar μ) (hadm : IsAdmissible σ)
    (P : IndSp (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) →ₗ[ℂ]
      IndSp (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) →ₗ[ℂ] ℂ)
    (hP : ∀ (h : GL (Fin (r + t)) k) a f,
      P (parInd (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) h a)
        (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f) = P a f)
    (hQ : ∀ a, (∀ f, P a f = 0) → a = 0)
    (Φ₀ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w₀ : V)
    (hne : famF hσ hs hp hu hI hμ Φ₀ w₀ ≠ 0) :
    ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) := by sorry
