-- Prove2me | Theorems.Thm_GlobalTheory_FontCmp_fontaineFormalism_equiv
-- name    : GlobalTheory.FontCmp.fontaineFormalism_equiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:28:23.717353+00:00
-- url     : https://prove2.me/theorems/8de6aa87-9ba6-404b-9ff8-1956e21b2e6d
-- title:
--   Font Cmp: fontaine Formalism equiv
-- statement:
--   The Font Cmp construction uses the fontaine Formalism equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineFormalismTensorEquiv.lean#L667-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FontaineFormalismTensorEquiv.lean#L667-L669

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

theorem GlobalTheory.FontCmp.fontaineFormalism_equiv : CrystallineSubrepresentation.FontaineFormalism l P ↔ TensorMultiplication.FontaineFormalism l P := by sorry
