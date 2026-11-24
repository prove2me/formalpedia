-- Prove2me | Theorems.Thm_GlobalTheory_SS_dilatation_lowers_defect
-- name    : GlobalTheory.SS.dilatation_lowers_defect
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:37.466913+00:00
-- url     : https://prove2.me/theorems/8e982621-66ee-4d5c-a6f9-7e02f562db4b
-- title:
--   SS: dilatation lowers defect
-- statement:
--   The SS construction uses the dilatation lowers defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L561-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L561-L627

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS
open Dil

theorem GlobalTheory.SS.dilatation_lowers_defect : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (E : ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop), (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') → ∀ (I : Ideal B), (∀ b, b ∈ I ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b) → ∀ (k : Type) [Field k] [Algebra R k] [Algebra k (B ⧸ I)] [IsScalarTower R k (B ⧸ I)], Function.Surjective (algebraMap R k) → Algebra.Smooth k (B ⧸ I) → Module.Free (B ⧸ I) (TensorProduct B (B ⧸ I) (KaehlerDifferential R B)) → ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (c : ℕ), E R' a → Defect a π (c + 1) → ∃ a' : B' →ₐ[R] R', a'.comp φ = a ∧ Defect a' π c := by sorry
