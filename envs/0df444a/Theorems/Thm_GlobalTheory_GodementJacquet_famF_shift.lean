-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_famF_shift
-- name    : GlobalTheory.GodementJacquet.famF_shift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:48.610976+00:00
-- url     : https://prove2.me/theorems/8f3fe8b4-5abd-4094-8cd8-58184903c469
-- title:
--   Godement Jacquet: fam F shift
-- statement:
--   The Godement Jacquet construction uses the fam F shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairDetTwist.lean#L435-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairDetTwist.lean#L435-L441

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
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
variable [m.IsMulLeftInvariant] (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
      Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)

theorem GlobalTheory.GodementJacquet.famF_shift [m.IsMulRightInvariant] (hμ : IsSmoothChar μ)
    (Φ Φ' : SB (Matrix (Fin (r + t)) (Fin r) k)) (g₀ : GL (Fin r) k)
    (hΦ : Φ'.1 = om μ g₀ 1 Φ.1) (w : V) :
    famF hσ hs hp hu hI hμ Φ' w = famF hσ hs hp hu hI hμ Φ (σ g₀⁻¹ w) := by sorry
