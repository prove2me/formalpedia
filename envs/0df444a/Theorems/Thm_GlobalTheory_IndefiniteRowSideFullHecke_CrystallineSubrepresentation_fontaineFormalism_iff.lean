-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineSubrepresentation_fontaineFormalism_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.fontaineFormalism_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:24.648542+00:00
-- url     : https://prove2.me/theorems/15f03d94-2994-4622-970f-fbad10601cdd
-- title:
--   Crystalline Subrepresentation: fontaine Formalism iff
-- statement:
--   The Crystalline Subrepresentation construction uses the fontaine Formalism iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineSubrepresentation.lean#L234-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineSubrepresentation.lean#L234-L243

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

theorem GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.fontaineFormalism_iff :
    FontaineFormalism l P ↔ ∀ K LL : FinExt l, FormalismFor (P.PD K) ↥LL.1 := by sorry
