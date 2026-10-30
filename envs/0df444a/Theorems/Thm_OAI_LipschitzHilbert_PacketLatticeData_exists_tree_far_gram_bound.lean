-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_tree_far_gram_bound
-- name    : OAI.LipschitzHilbert.PacketLatticeData.exists_tree_far_gram_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:39:23.596685+00:00
-- url     : https://prove2.me/theorems/64510062-9b22-4a11-907e-a22ed65784e5
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.exists_tree_far_gram_bound: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.exists_tree_far_gram_bound` of [lean/OAI/Analysis/LipschitzHilbert/Geometry/PacketDataTreeFarEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Geometry/PacketDataTreeFarEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_tree_far_gram_bound (hL : LepingleInput)
--       (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
--       (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
--       ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : PacketLatticeData N κ Label Item) (M Q : ℕ), Cb≤Q →
--         ∀ (t w a b L F sigma K : ℝ), 0<w → 0<L → 0≤F → Cb*w≤P.width →
--         (∀ k, |P.frequency k|≤F/w) →
--         (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
--       ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
--         (S T : Finset P.PacketIndex) (gap : ℕ),
--         (∀ q∈T, P.length q.1≤L) →
--         (∀ q∈T, |P.actualX q.1 q.2.1 q.2.2-a|≤L) →
--         (∀ q∈T, |(P.actualZ q.1 q.2.1 q.2.2-b)-t*(P.actualX q.1 q.2.1 q.2.2-a)|≤P.width) →
--         (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
--           |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
--         (∀ q∈T, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| ∧
--           |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
--         (∀ q∈S, ‖c q.1 q.2.1 q.2.2‖ ≤ sigma) →
--         (∀ q∈S, |(P.rowSlope q.1 q.2.1-t)*P.length q.1/P.width|≤1) →
--         (∀ q∈S, P.length q.1≤L) →
--         (∀ z : ℝ×ℝ, ((S.filter fun q => |z.1-P.actualX q.1 q.2.1 q.2.2|≤P.length q.1 ∧
--           |(z.2-P.actualZ q.1 q.2.1 q.2.2)-t*(z.1-P.actualX q.1 q.2.1 q.2.2)|≤P.width).card:ℝ)≤K) →
--         ‖∑ q∈S, ∫ z, inner ℂ (P.packetVector c q z) (P.longPacketSum c T gap q.1 z)
--           ∂volume.prod volume‖^2≤
--           (4*P.profileBound*sigma)^2*256*(82944*K)^2*1296*Real.pi^2*L*P.width*
--             ((((2*Q+1)*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2*
--               ∑ q∈T, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.actualX`, `OAI.LipschitzHilbert.PacketLatticeData.actualZ`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.longPacketSum`, `OAI.LipschitzHilbert.PacketLatticeData.packetVector`, `OAI.LipschitzHilbert.PacketLatticeData.physicalPacket`, `OAI.LipschitzHilbert.PacketLatticeData.referenceEnvelopeConstant` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split).
--
--   **Used by.** The proofs of `OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step` and `OAI.LipschitzHilbert.PacketLatticeData.exists_universal_ordinary_model_estimate` of this split import it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Geometry/PacketDataTreeFarEnergy.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.exists_tree_far_gram_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000

section

attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem exists_tree_far_gram_bound (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M Q : ℕ), Cb≤Q →
      ∀ (t w a b L F sigma K : ℝ), 0<w → 0<L → 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (S T : Finset P.PacketIndex) (gap : ℕ),
      (∀ q∈T, P.length q.1≤L) →
      (∀ q∈T, |P.actualX q.1 q.2.1 q.2.2-a|≤L) →
      (∀ q∈T, |(P.actualZ q.1 q.2.1 q.2.2-b)-t*(P.actualX q.1 q.2.1 q.2.2-a)|≤P.width) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ q∈T, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| ∧
        |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      (∀ q∈S, ‖c q.1 q.2.1 q.2.2‖ ≤ sigma) →
      (∀ q∈S, |(P.rowSlope q.1 q.2.1-t)*P.length q.1/P.width|≤1) →
      (∀ q∈S, P.length q.1≤L) →
      (∀ z : ℝ×ℝ, ((S.filter fun q => |z.1-P.actualX q.1 q.2.1 q.2.2|≤P.length q.1 ∧
        |(z.2-P.actualZ q.1 q.2.1 q.2.2)-t*(z.1-P.actualX q.1 q.2.1 q.2.2)|≤P.width).card:ℝ)≤K) →
      ‖∑ q∈S, ∫ z, inner ℂ (P.packetVector c q z) (P.longPacketSum c T gap q.1 z)
        ∂volume.prod volume‖^2≤
        (4*P.profileBound*sigma)^2*256*(82944*K)^2*1296*Real.pi^2*L*P.width*
          ((((2*Q+1)*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2*
            ∑ q∈T, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width) := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
