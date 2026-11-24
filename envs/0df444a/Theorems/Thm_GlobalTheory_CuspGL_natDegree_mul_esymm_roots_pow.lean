-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_natDegree_mul_esymm_roots_pow
-- name    : GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:32:25.014547+00:00
-- url     : https://prove2.me/theorems/ccc19c4b-481e-401f-94af-f04c79301668
-- title:
--   Cusp GL: nat Degree mul esymm roots pow
-- statement:
--   The Cusp GL construction uses the nat Degree mul esymm roots pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeMulEsymmRootsPow.lean#L36-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeMulEsymmRootsPow.lean#L36-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by sorry
