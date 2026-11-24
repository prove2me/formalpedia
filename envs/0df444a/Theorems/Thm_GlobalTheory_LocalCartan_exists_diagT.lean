-- Prove2me | Theorems.Thm_GlobalTheory_LocalCartan_exists_diagT
-- name    : GlobalTheory.LocalCartan.exists_diagT
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:02:15.639197+00:00
-- url     : https://prove2.me/theorems/ba95204e-da08-45b6-a074-ac4c85d8560b
-- title:
--   Local Cartan: exists diag T
-- statement:
--   The Local Cartan construction uses the exists diag T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ValuationDivZpowOrd.lean#L38-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ValuationDivZpowOrd.lean#L38-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open GlobalTheory GlobalTheory.LocalCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.LocalCartan.exists_diagT (g : GL n k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ t : n → kˣ, g = x * _root_.GlobalTheory.SmGL.diagT k n t * y := by sorry
