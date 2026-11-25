-- Prove2me | Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
-- name    : GlobalTheory.FlagMahler.comp_le_Qy
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:37.838524+00:00
-- url     : https://prove2.me/theorems/204f1ec2-9409-4633-9a6b-7265e85efe15
-- title:
--   Flag Mahler: comp le Qy
-- statement:
--   The Flag Mahler construction uses the comp le Qy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L114-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L114-L127

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
open NumberField Module
open Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
open Complex

theorem GlobalTheory.FlagMahler.comp_le_Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ)
    (p : Fin r → E) (b : Fin r) :
    X.c τ * ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) b‖ ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y p := by sorry
