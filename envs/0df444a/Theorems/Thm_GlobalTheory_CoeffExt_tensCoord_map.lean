-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_tensCoord_map
-- name    : GlobalTheory.CoeffExt.tensCoord_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:56.238012+00:00
-- url     : https://prove2.me/theorems/9284b885-d478-4fbc-87fb-06834e0c984f
-- title:
--   Coeff Ext: tens Coord map
-- statement:
--   The Coeff Ext construction uses the tens Coord map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L106-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L106-L114

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {Qp : Type} [Field Qp] {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
  [Algebra Qp LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  [Module LL' V'] [IsScalarTower Qp LL' V']
  {ι : Type} [Fintype ι] [DecidableEq ι] (E : V' ≃ₗ[LL] (ι → V))

theorem GlobalTheory.CoeffExt.tensCoord_map {C D : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup D] [Module Qp D]
    (φ' : V' →ₗ[LL'] V') (φ : V →ₗ[LL] V) (h : ∀ x i, E (φ' x) i = φ (E x i)) (ψ : C →ₗ[Qp] D)
    (x : V' ⊗[Qp] C) (i : ι) :
    tensCoord E D (AlgebraTensorModule.map φ' ψ x) i =
      AlgebraTensorModule.map φ ψ (tensCoord E C x i) := by sorry
