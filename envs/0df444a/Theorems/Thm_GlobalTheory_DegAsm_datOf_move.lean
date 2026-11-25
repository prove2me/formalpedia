-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_datOf_move
-- name    : GlobalTheory.DegAsm.datOf_move
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:23:30.514069+00:00
-- url     : https://prove2.me/theorems/32ac973b-1ffd-43ee-9947-024e9369cdd0
-- title:
--   Deg Asm: dat Of move
-- statement:
--   The Deg Asm construction uses the dat Of move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotent.lean#L137-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotent.lean#L137-L230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
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
open AdaptInv DatMove

theorem GlobalTheory.DegAsm.datOf_move : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by sorry
