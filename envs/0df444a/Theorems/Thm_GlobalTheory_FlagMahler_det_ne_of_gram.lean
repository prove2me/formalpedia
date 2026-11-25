-- Prove2me | Theorems.Thm_GlobalTheory_FlagMahler_det_ne_of_gram
-- name    : GlobalTheory.FlagMahler.det_ne_of_gram
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:07:22.496549+00:00
-- url     : https://prove2.me/theorems/45f4fbbc-78a8-49f4-961f-714af7b71461
-- title:
--   Flag Mahler: det ne of gram
-- statement:
--   The Flag Mahler construction uses the det ne of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L186-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L186-L205

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlagMahler
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open Complex

theorem GlobalTheory.FlagMahler.det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by sorry
