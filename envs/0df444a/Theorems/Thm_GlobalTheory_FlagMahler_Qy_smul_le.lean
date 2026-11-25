-- Prove2me | Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
-- name    : GlobalTheory.FlagMahler.Qy_smul_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:00.482783+00:00
-- url     : https://prove2.me/theorems/cfd7656d-371d-58ab-a430-c25dc5320723
-- title:
--   Flag Mahler: Qy smul le
-- statement:
--   The Flag Mahler construction uses the Qy smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L247-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L247-L264

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
open NumberField Module
open Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem GlobalTheory.FlagMahler.Qy_smul_le (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (α : E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (α • v) ≤ (∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v := by sorry
