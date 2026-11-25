-- Prove2me | Theorems.Thm_GlobalTheory_T_isSemisimpleRepresentation_of_iSup_range_equivariant
-- name    : GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:51.193606+00:00
-- url     : https://prove2.me/theorems/ee52824b-8b63-4f21-9a17-876a053a30ca
-- title:
--   T: is Semisimple Representation of i Sup range equivariant
-- statement:
--   The T construction uses the is Semisimple Representation of i Sup range equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationOfISupRangeEquivariantStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSemisimpleRepresentationOfISupRangeEquivariantStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant : ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by sorry
