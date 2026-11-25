-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PrimPerp_perp_prim
-- name    : GlobalTheory.DegCnt.PrimPerp.perp_prim
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:42:34.7588+00:00
-- url     : https://prove2.me/theorems/ddfd666f-2388-41ea-b546-f0d4df5634c1
-- title:
--   Prim Perp: perp prim
-- statement:
--   The Prim Perp construction uses the perp prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagPairDefinitePartLatticeDiscriminantEqQuotien.lean#L36-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FlagPairDefinitePartLatticeDiscriminantEqQuotien.lean#L36-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IdxSupRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagPairDefinitePartLatticeDiscriminantEqQuotien
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PrimPerp
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.PrimPerp.perp_prim (H : HermSpace K V) [IsTotallyComplex K] {M : Submodule (𝓞 K) V} {S I W : Submodule K V}
    (hIS : I ≤ S) (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {z : V} {T : ℕ} (hT : 1 ≤ T) (hz : H.B z z = -(T : K))
    (hp : ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K))
    (hW : ∀ y, y ∈ W ↔ y ∈ S ∧ H.B y z = 0) :
    del H (M ⊓ rs (𝓞 K) W) = (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ∧
      GenBy (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) 1 ∧ IsLatMod (M ⊓ rs (𝓞 K) W) W I ∧
      Nonempty ((↥(dual H (M ⊓ rs (𝓞 K) W)) ⧸ (M ⊓ rs (𝓞 K) W).comap (dual H (M ⊓ rs (𝓞 K) W)).subtype) ≃ₗ[𝓞 K]
        (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) := by sorry
