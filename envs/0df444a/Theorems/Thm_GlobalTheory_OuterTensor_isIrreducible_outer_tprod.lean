-- Prove2me | Theorems.Thm_GlobalTheory_OuterTensor_isIrreducible_outer_tprod
-- name    : GlobalTheory.OuterTensor.isIrreducible_outer_tprod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:47.589302+00:00
-- url     : https://prove2.me/theorems/d6e73e1f-19fd-4ff9-96ff-7d83039f255c
-- title:
--   Outer Tensor: is Irreducible outer tprod
-- statement:
--   The Outer Tensor construction uses the is Irreducible outer tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleOuterTprod.lean#L14-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleOuterTprod.lean#L14-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleOuterTprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.OuterTensor

theorem GlobalTheory.OuterTensor.isIrreducible_outer_tprod :
    ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W), ρ.IsIrreducible → σ.IsIrreducible → (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IsIrreducible := by sorry
