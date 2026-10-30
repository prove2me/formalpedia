-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_assigned_parent_central_gain
-- name    : OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:36:03.939714+00:00
-- url     : https://prove2.me/theorems/8b60fa99-6a70-45a0-94ce-b3b05b0953b1
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain` of [lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataAssignedParentCentralGain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataAssignedParentCentralGain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology ENNReal`):
--
--   ```lean
--   theorem eventually_assigned_parent_central_gain
--       (pProfile qEnv Cmass Cweight F c0 A_M d m decay : ℝ) (Dweight Kcount Hcount : ℕ)
--       (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
--       (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
--       (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
--       (hDweight : 2 < (Dweight:ℝ)) (hd : 0 ≤ d) (hm : 0 ≤ m)
--       (hqm : 2*(qEnv+6)+2 ≤ m) (hCmassM : Cmass ≤ m) (hdecay : 0 ≤ decay) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
--         (P : PacketLatticeData N κ Label Item),
--       ∀ (tops : Finset τ) (T : τ → SlopeBox)
--         (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
--         (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
--         (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
--         (∀ k, c0/w ≤ |P.frequency k|) →
--         (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
--       ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
--         (b : ∀ j, P.labels j → κ → ℝ → ℂ),
--         (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
--         (∀ j l k s, b j l k s ≠ 0 →
--           |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
--       ∀ (v : ℝ×ℝ → ℝ), Measurable v →
--       ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
--       ∀ (maskExponent shortVariation : ℝ), 0 ≤ maskExponent →
--       let Kw := L^(maskExponent+2)
--       let R := fun t => (T t).length
--       let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
--         hw hcone hF hwide hfrequency
--       let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
--         hw hcone hF hwide hfrequency
--       let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
--         hw hcone hF hwide hfrequency alt
--       let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
--         hw hcone hF hwide hfrequency alt hAlt
--       ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
--         (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
--       cone ≤ Kcount →
--       (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
--         (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
--       (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
--       3+2*(8*Dweight+1) ≤ P.order →
--       (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
--       (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
--         Kw*(T (assigned u)).length) →
--       (∀ u ∈ packets,
--         |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
--           ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
--         Kw*(T (assigned u)).width) →
--       (∀ u ∈ packets, assigned u ∈ tops) →
--       (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
--       (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
--         (R (assigned u)) cone w u.1 u.2.1) →
--       ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
--         (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
--         (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
--         (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
--           (w/(T t).length) 0) →
--       ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
--       ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → Dphase ≤ L^d → 0 < Nmass → Real.log Nmass ≤ 2*L →
--         0 ≤ A → A ≤ L^qEnv →
--       let p := Real.sqrt L
--       let mu := PhaseCombinatorics.phaseMu Dphase p
--       let a := mu/(SourceParameters.blockCount L:ℝ)
--       let cut := g.rootWidth/(SourceParameters.branching L)^2
--       let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
--       let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
--       let original := P.physicalMaskedValue alt hAlt oldSlope b v f
--         (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
--       let countTop := fun shift => g.sourceTopTerminalCount T cut w hw hKb shift
--       let count := fun shift => tops.sup (countTop shift)
--       ∀ (Z0 : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ)), MeasurableSet Z0 →
--         (∀ t ∈ tops, MeasurableSet (bad t)) →
--       let good := sourceGoodPathSet Z0 tops weight bad L
--       (∀ z ∈ Z0, ∀ t ∈ tops, weight t z ≤ Cweight) →
--       (∀ z ∈ Z0, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
--       (∀ z ∈ Z0, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
--       (∀ z ∈ Z0, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
--         |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
--         let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
--           (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
--           0 lower upper
--         ‖V z.1 yy‖+(T t).width*
--           ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
--       (∀ shift, ∀ j < count shift, ∀ z ∈ Z0, ∀ I : Finset τ, I ⊆ tops →
--         (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
--         (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
--           (SourceParameters.branching L)^2) →
--         (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*
--           g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
--         (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
--           g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |(T t).slope-(T u).slope|) →
--         (I.card:ℝ) ≤ Dphase/100) →
--       let squarePackets := fun t => sourceReferencePackets packets (fun u => P.length u.1)
--         (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R t) (T t).slope
--         (cone+(SourceParameters.branching L)^3) w
--       let Qsquare := fun t => P.referenceFamily oldSlope (T t).slope (R t)
--         (cone+(SourceParameters.branching L)^3) w F hw
--         (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
--       let origSquare := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
--         (cone+(SourceParameters.branching L)^3) w
--       let squareSelected := fun t => (Finset.univ : Finset (Qsquare t).PacketIndex).filter
--         (fun u => (⟨u.1,⟨origSquare t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets t)
--       let S := fun shift t => g.fixedPathResidualPackets tops (fun u => (T u).slope)
--         (fun u => w/(T u).length) cut packets assigned (fun u => stop u.1)
--         (ShiftedBlocks.endpoint shift) (countTop shift t-1) (T t).slope
--       let Qref := fun t => P.referenceFamily oldSlope (T t).slope (R t)
--         (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
--       let origRef := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
--         (cone+(SourceParameters.branching L)^2) w
--       let selected := fun shift t => (Finset.univ : Finset (Qref t).PacketIndex).filter
--         (fun u => (⟨u.1,⟨origRef t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S shift t)
--       (∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qsquare t).restrictPackets (squareSelected t)).physicalReferenceBad
--         ((Qsquare t).restrictedAlternate (fun j l => alt j (origSquare t j l)) (squareSelected t))
--         ((Qsquare t).restrictedAlternate_bound (fun j l => alt j (origSquare t j l))
--           (fun j l => hAlt j (origSquare t j l)) (squareSelected t))
--         (T t).slope (w/P.topLength) (fun j l => b j (origSquare t j l)) v f
--         (fun j l u => T (assigned ⟨j,⟨origSquare t j l,u.val⟩⟩))
--         L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
--       (∀ shift, ∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qref t).restrictPackets (selected shift t)).physicalReferenceBad
--         ((Qref t).restrictedAlternate (fun j l => alt j (origRef t j l)) (selected shift t))
--         ((Qref t).restrictedAlternate_bound (fun j l => alt j (origRef t j l))
--           (fun j l => hAlt j (origRef t j l)) (selected shift t))
--         (T t).slope (w/P.topLength) (fun j l => b j (origRef t j l)) v f
--         (fun j l u => T (assigned ⟨j,⟨origRef t j l,u.val⟩⟩))
--         L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
--       ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
--         (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
--         (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
--         (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
--       let W := fun z => ∑ s ∈ packets,
--         ((g.sourceBoundaryCoefficient tops (fun t => (T t).slope) (fun t => w/(T t).length)
--           cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
--           (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
--       IntegrableOn (fun z => ‖W z‖) good (volume.prod volume) ∧
--         (∫ z in good, ‖W z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.sourceReferencePackets`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.AngularGrid.fixedPathResidualPackets`, `OAI.LipschitzHilbert.AngularGrid.lastEligible`, `OAI.LipschitzHilbert.AngularGrid.sourceBoundaryCoefficient`, `OAI.LipschitzHilbert.AngularGrid.sourceBoundaryGap`, `OAI.LipschitzHilbert.AngularGrid.sourceGap`, `OAI.LipschitzHilbert.AngularGrid.sourceTopTerminalCount`, `OAI.LipschitzHilbert.PacketLatticeData.AssignedTopItem`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.actualX`, `OAI.LipschitzHilbert.PacketLatticeData.actualZ`, `OAI.LipschitzHilbert.PacketLatticeData.assignedReferenceAlternate`, `OAI.LipschitzHilbert.PacketLatticeData.assignedReferenceAlternate_bound`, `OAI.LipschitzHilbert.PacketLatticeData.assignedReferenceFamily`, `OAI.LipschitzHilbert.PacketLatticeData.assignedReferenceOriginalLabel`, `OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.length_pos`, `OAI.LipschitzHilbert.PacketLatticeData.physicalMaskedValue`, `OAI.LipschitzHilbert.PacketLatticeData.physicalMultiplierCoefficient`, `OAI.LipschitzHilbert.PacketLatticeData.referenceCondition`, `OAI.LipschitzHilbert.PacketLatticeData.referenceEnvelopeConstant`, `OAI.LipschitzHilbert.PacketLatticeData.referenceFamily`, `OAI.LipschitzHilbert.PacketLatticeData.referenceLabels`, `OAI.LipschitzHilbert.PacketLatticeData.referenceOriginalLabel`, `OAI.LipschitzHilbert.ShiftedBlocks.endpoint`, `OAI.LipschitzHilbert.SlopeBox.radius`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceLabeledLattice.PacketIndex`, `OAI.LipschitzHilbert.SourceLabeledLattice.RestrictedPacketItem`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalReferenceBad`, `OAI.LipschitzHilbert.SourceLabeledLattice.rawInterval`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictPackets`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictedAlternate`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictedAlternate_bound`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype`, `OAI.LipschitzHilbert.SourceLabeledLattice.withProfile`, `OAI.LipschitzHilbert.SourceParameters.blockCount`, `OAI.LipschitzHilbert.SourceParameters.branching`, `OAI.LipschitzHilbert.SourceParameters.branching_pos`, `OAI.LipschitzHilbert.SourceParameters.step` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.covariantSignal`, `OAI.LipschitzHilbert.sourceGoodPathSet` and `OAI.LipschitzHilbert.PhaseCombinatorics.phaseMu` (definitions bundle `OAIQ090A001` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataAssignedParentCentralGain.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_central_gain
    (pProfile qEnv Cmass Cweight F c0 A_M d m decay : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hqm : 2*(qEnv+6)+2 ≤ m) (hCmassM : Cmass ≤ m) (hdecay : 0 ≤ decay) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item),
    ∀ (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent shortVariation : ℝ), 0 ≤ maskExponent →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    cone ≤ Kcount →
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → Dphase ≤ L^d → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := fun shift => g.sourceTopTerminalCount T cut w hw hKb shift
    let count := fun shift => tops.sup (countTop shift)
    ∀ (Z0 : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ)), MeasurableSet Z0 →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
    let good := sourceGoodPathSet Z0 tops weight bad L
    (∀ z ∈ Z0, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ Z0, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ Z0, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ Z0, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ shift, ∀ j < count shift, ∀ z ∈ Z0, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    let squarePackets := fun t => sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R t) (T t).slope
      (cone+(SourceParameters.branching L)^3) w
    let Qsquare := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w F hw
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
    let origSquare := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w
    let squareSelected := fun t => (Finset.univ : Finset (Qsquare t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets t)
    let S := fun shift t => g.fixedPathResidualPackets tops (fun u => (T u).slope)
      (fun u => w/(T u).length) cut packets assigned (fun u => stop u.1)
      (ShiftedBlocks.endpoint shift) (countTop shift t-1) (T t).slope
    let Qref := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w
    let selected := fun shift t => (Finset.univ : Finset (Qref t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S shift t)
    (∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qsquare t).restrictPackets (squareSelected t)).physicalReferenceBad
      ((Qsquare t).restrictedAlternate (fun j l => alt j (origSquare t j l)) (squareSelected t))
      ((Qsquare t).restrictedAlternate_bound (fun j l => alt j (origSquare t j l))
        (fun j l => hAlt j (origSquare t j l)) (squareSelected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origSquare t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ shift, ∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qref t).restrictPackets (selected shift t)).physicalReferenceBad
      ((Qref t).restrictedAlternate (fun j l => alt j (origRef t j l)) (selected shift t))
      ((Qref t).restrictedAlternate_bound (fun j l => alt j (origRef t j l))
        (fun j l => hAlt j (origRef t j l)) (selected shift t))
      (T t).slope (w/P.topLength) (fun j l => b j (origRef t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
      (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
      (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
      (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
    let W := fun z => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
        (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
    IntegrableOn (fun z => ‖W z‖) good (volume.prod volume) ∧
      (∫ z in good, ‖W z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
