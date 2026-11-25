-- Prove2me | Theorems.Thm_GlobalTheory_WachTie_exists_invariant_basis
-- name    : GlobalTheory.WachTie.exists_invariant_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:41.077811+00:00
-- url     : https://prove2.me/theorems/3e8e0479-2c03-4c62-ae17-35bbd1f8d32a
-- title:
--   Wach Tie: exists invariant basis
-- statement:
--   The Wach Tie construction uses the exists invariant basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisAddPiSmul.lean#L13-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisAddPiSmul.lean#L13-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoordApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisAddPiSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie
open GlobalTheory GlobalTheory.WachTie
open PowerSeries

theorem GlobalTheory.WachTie.exists_invariant_basis : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}, IsUnit (W.DelF.card : O) → Nonempty (Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) → ∃ b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T), ∀ k, (b k : W.DD T) ∈ W.NΔ T := by sorry
