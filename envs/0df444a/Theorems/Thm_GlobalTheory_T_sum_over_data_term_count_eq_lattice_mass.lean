-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_over_data_term_count_eq_lattice_mass
-- name    : GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:48:18.39989+00:00
-- url     : https://prove2.me/theorems/83f4c70a-61aa-45d0-a5ca-fffbee734d32
-- title:
--   T: sum over data term count eq lattice mass
-- statement:
--   The T construction uses the sum over data term count eq lattice mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumOverDataTermCountEqLatticeMassStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumOverDataTermCountEqLatticeMassStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumOverDataTermCountEqLatticeMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumOverDataTermCountEqLatticeMassStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (C : Set S.FrP) (P : S.Datum → Submodule L.O S.V → Prop), (∀ h ∈ S.H0, ∀ d Λ, S.IsTerm d Λ → P d Λ → P (h • d) (h • Λ)) → (S.sumData fun d => S.nT d C (P d)) = ∑' o : MulAction.orbitRel.Quotient S.H0 (Submodule L.O S.V), if ∃ d, S.IsTerm d o.out ∧ P d o.out ∧ S.Fr d o.out = C then ENNReal.ofReal (invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV o.out)) else 0 := by sorry
