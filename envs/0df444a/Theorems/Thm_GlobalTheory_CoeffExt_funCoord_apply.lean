-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_funCoord_apply
-- name    : GlobalTheory.CoeffExt.funCoord_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:51.292307+00:00
-- url     : https://prove2.me/theorems/4a59522d-1f32-4ea9-8143-c0b484717c41
-- title:
--   Coeff Ext: fun Coord apply
-- statement:
--   The Coeff Ext construction uses the fun Coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L294-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L294-L295

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
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  {V V' : Type} [AddCommGroup V] [AddCommGroup V'] [Module LL V] [Module LL V'] [Module O V]
  [Module O V'] [IsScalarTower O LL V] [IsScalarTower O LL V'] {ι : Type}

theorem GlobalTheory.CoeffExt.funCoord_apply (G : Type) (E : V' ≃ₗ[LL] (ι → V)) (c : G → V') (i : ι) (g : G) :
    funCoord O G E c i g = E (c g) i := by sorry

attribute [defeq] GlobalTheory.CoeffExt.funCoord_apply
