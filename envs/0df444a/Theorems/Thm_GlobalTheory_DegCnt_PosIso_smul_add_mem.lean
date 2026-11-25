-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosIso_smul_add_mem
-- name    : GlobalTheory.DegCnt.PosIso.smul_add_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:24:54.679997+00:00
-- url     : https://prove2.me/theorems/5a4be067-4cf2-48b1-a706-fca99e6bd380
-- title:
--   Pos Iso: smul add mem
-- statement:
--   The Pos Iso construction uses the smul add mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L545-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean#L545-L557

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

theorem GlobalTheory.DegCnt.PosIso.smul_add_mem (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : 𝓞 K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      (γ : K) * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {y ξ : V} (hy : ∀ u ∈ N.F'.X, H.B y u = 0) (hξ : ξ ∈ N.F.Xa N.j) (h : y - ξ ∈ Λ) : γ • y ∈ Λ := by sorry
