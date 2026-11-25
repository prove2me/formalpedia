-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_adapt_invariants
-- name    : GlobalTheory.DegAsm.adapt_invariants
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:07.06941+00:00
-- url     : https://prove2.me/theorems/38320b4e-7ac0-4ed8-8ee2-85cf12ed559f
-- title:
--   Deg Asm: adapt invariants
-- statement:
--   The Deg Asm construction uses the adapt invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagFramesSameGradedDefinitePartLatticeEq.lean#L366-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagFramesSameGradedDefinitePartLatticeEq.lean#L366-L393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm
open AdaptInv
open NumberField
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.DegAsm.adapt_invariants : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : _root_.GlobalTheory.DegCnt.NF H r), _root_.GlobalTheory.DegAsm.Adapt F F' 𝔡 N → (∀ a : ℕ, N.F.Xa a = F.Xa a ∧ N.F'.Xa a = F'.Xa a) ∧ N.F.X = F.X ∧ N.F'.X = F'.X ∧ _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' = _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' ∧ N.j = r - Module.finrank K (_root_.Formalism.HermitianLatticeCounting.S6.II F F') ∧ (∀ (l : ℕ) (hl : l ≤ r + 1), _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl) ∧ (∀ (l : ℕ) (hl : l ≤ r + 1), N.j < l → l ≤ r → _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl = 0) ∧ (∀ s : V →ₗ[K] V, (N.F.InN s ↔ F.InN s) ∧ (N.F'.InN s ↔ F'.InN s)) ∧ ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), (N.IsTerm g Λ ↔ _root_.GlobalTheory.HermLat.IsFramed F F' Λ N.aa ∧ _root_.GlobalTheory.HermLat.IsAdm F F' Λ (g : 𝓞 K)) ∧ _root_.GlobalTheory.HermLat.latL N.F N.F' Λ = _root_.GlobalTheory.HermLat.latL F F' Λ ∧ _root_.GlobalTheory.HermLat.latL N.F' N.F Λ = _root_.GlobalTheory.HermLat.latL F' F Λ ∧ _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice N.F N.F' Λ = _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice F F' Λ ∧ _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice N.F' N.F Λ = _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice F' F Λ ∧ _root_.GlobalTheory.HermLat.iotaGraph N.F N.F' Λ (g : 𝓞 K) = _root_.GlobalTheory.HermLat.iotaGraph F F' Λ (g : 𝓞 K) := by sorry
