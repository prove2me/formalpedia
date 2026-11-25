-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLeast_nval_le_of_val
-- name    : GlobalTheory.ThetaLeast.nval_le_of_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:59.188374+00:00
-- url     : https://prove2.me/theorems/fc3ff493-7322-431f-9562-6084201964af
-- title:
--   Theta Least: nval le of val
-- statement:
--   The Theta Least construction uses the nval le of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L153-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L153-L169

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

theorem GlobalTheory.ThetaLeast.nval_le_of_val (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ))
    {x z : T.Fr} (hx : x ≠ 0) {ε : F} (hε : 0 ≤ v ε) {ρ : ℚ} (hρ : v (ε * algebraMap T.Fr F z) = (ρ : WithTop ℚ))
    {δ : ℝ} (hle : (ρ : ℝ) ≤ ((vV T.V x : ℤ) : ℚ) + δ) (e : ℕ) :
    nval T.V e z ≤ nval T.V e x + ((δ / e : ℝ) : EReal) := by sorry
