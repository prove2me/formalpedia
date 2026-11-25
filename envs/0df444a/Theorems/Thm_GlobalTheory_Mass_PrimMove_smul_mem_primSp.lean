-- Prove2me | Theorems.Thm_GlobalTheory_Mass_PrimMove_smul_mem_primSp
-- name    : GlobalTheory.Mass.PrimMove.smul_mem_primSp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:21.492903+00:00
-- url     : https://prove2.me/theorems/a0b55123-6508-4c0a-9c8a-b4d3dec23a63
-- title:
--   Prim Move: smul mem prim Sp
-- statement:
--   The Prim Move construction uses the smul mem prim Sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveSublatticesMoveWithIsometries.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveSublatticesMoveWithIsometries.lean#L58-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveSublatticesMoveWithIsometries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimMove
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem GlobalTheory.Mass.PrimMove.smul_mem_primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V)
    (U : Submodule K V) (j n : ℕ) : g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n := by sorry
