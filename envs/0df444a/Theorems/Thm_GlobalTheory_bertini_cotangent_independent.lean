-- Prove2me | Theorems.Thm_GlobalTheory_bertini_cotangent_independent
-- name    : GlobalTheory.bertini_cotangent_independent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:53.006831+00:00
-- url     : https://prove2.me/theorems/9d3ab9c3-c731-5143-8dbf-76a889a17419
-- title:
--   Global Theory: bertini cotangent independent
-- statement:
--   The Global Theory construction uses the bertini cotangent independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GenericResidueLinearIndependence.lean#L85-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GenericResidueLinearIndependence.lean#L85-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GenericResidueLinearIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.bertini_cotangent_independent : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ), ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (q : Ideal A) [q.IsPrime] (R : Type) [CommRing R] [IsLocalRing R] [Algebra A R] [IsLocalization.AtPrime R q], (∃ p, f p ∉ q) → LinearIndependent (IsLocalRing.ResidueField R) (fun j : {j : Fin M // algebraMap A R (∑ p, u (j, p) • f p) ∈ IsLocalRing.maximalIdeal R} => ((IsLocalRing.maximalIdeal R).toCotangent ⟨_, j.2⟩ : IsLocalRing.CotangentSpace R)) := by sorry
