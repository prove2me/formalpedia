-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosIso_smul_mem_of_pairing
-- name    : GlobalTheory.DegCnt.PosIso.smul_mem_of_pairing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:25:09.037918+00:00
-- url     : https://prove2.me/theorems/773c92c6-90cc-5da7-8ada-3e1d1b80bbb6
-- title:
--   Pos Iso: smul mem of pairing
-- statement:
--   The Pos Iso construction uses the smul mem of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L238-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L238-L283

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

theorem GlobalTheory.DegCnt.PosIso.smul_mem_of_pairing (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      γ * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {ξ : V} (hξ : ξ ∈ N.F.Xa N.j) (hp : ∀ y ∈ Λ, y ∈ N.F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    γ • ξ ∈ Λ := by sorry
