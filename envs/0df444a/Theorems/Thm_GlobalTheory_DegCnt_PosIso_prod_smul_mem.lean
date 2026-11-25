-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosIso_prod_smul_mem
-- name    : GlobalTheory.DegCnt.PosIso.prod_smul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:25:01.595798+00:00
-- url     : https://prove2.me/theorems/2490719a-1f69-5acd-b5d3-dac62b343b9c
-- title:
--   Pos Iso: prod smul mem
-- statement:
--   The Pos Iso construction uses the prod smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L192-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L192-L226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K]

theorem GlobalTheory.DegCnt.PosIso.prod_smul_mem (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (aa : Fin r → Submodule (𝓞 K) K)
    (hF : IsFrame F Λ aa) (hF' : IsFrame F' Λ aa)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K))
    {j : ℕ} (hj : j ≤ r) (s t : Fin j → K) (hs : ∀ a, s a ∈ aa (Fin.castLE hj a))
    (ht : ∀ a, t a ∈ aa (Fin.castLE hj a)) {ξ : V} (hξ : ξ ∈ F.Xa j)
    (hp : ∀ y ∈ Λ, y ∈ F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    ((∏ a, s a) * Dl F F' j (hj.trans (Nat.le_succ r)) * star (∏ a, t a)) • ξ ∈ Λ := by sorry
