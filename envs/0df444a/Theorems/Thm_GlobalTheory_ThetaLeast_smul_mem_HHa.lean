-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLeast_smul_mem_HHa
-- name    : GlobalTheory.ThetaLeast.smul_mem_HHa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:01.916345+00:00
-- url     : https://prove2.me/theorems/9329c008-2df7-45c2-82c7-f06f6b4a1735
-- title:
--   Theta Least: smul mem HHa
-- statement:
--   The Theta Least construction uses the smul mem HHa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L62-L66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast

theorem GlobalTheory.ThetaLeast.smul_mem_HHa {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] {cc : Ty → Ty} {isX : Ty → Prop}
    {a : Ty → ℕ → ℕ} (s : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    s • P ∈ HHa r n k cc isX a := by sorry
