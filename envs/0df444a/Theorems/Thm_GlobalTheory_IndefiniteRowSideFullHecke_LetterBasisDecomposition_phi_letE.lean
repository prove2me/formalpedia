-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LetterBasisDecomposition_phi_letE
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.phi_letE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:02:15.764196+00:00
-- url     : https://prove2.me/theorems/11a252b9-3fab-47b0-8376-3e194e8c6e98
-- title:
--   Letter Basis Decomposition: phi let E
-- statement:
--   The Letter Basis Decomposition construction uses the phi let E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/LettersFreeOfRank.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/LettersFreeOfRank.lean#L106-L111

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LettersFreeOfRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
attribute [local instance] letterModule
variable {W T}
variable (W T)

theorem GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.phi_letE (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by sorry
