-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_WachLettersFreeness_IsWachBasis_letter
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsWachBasis.letter
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:22.159614+00:00
-- url     : https://prove2.me/theorems/efd9da29-fe1e-4a84-a0e0-ee3b5ff876d8
-- title:
--   Is Wach Basis: letter
-- statement:
--   The Is Wach Basis construction uses the letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/WachLettersFree.lean#L40-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/WachLettersFree.lean#L40-L77

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachLettersFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsWachBasis.letter {r : ℕ} {b : Fin r → W.DD T} (hb : IsWachBasis W T b) (i : ZMod n) :
    IsLetterBasis W T i (fun k => (letE i : LetA O n) • b k) := by sorry
