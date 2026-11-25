-- Prove2me | Theorems.Thm_GlobalTheory_FlagMahler_finite_types
-- name    : GlobalTheory.FlagMahler.finite_types
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:21.401509+00:00
-- url     : https://prove2.me/theorems/9b67fd8e-ca4e-5ece-9bd7-f71bddf6f262
-- title:
--   Flag Mahler: finite types
-- statement:
--   The Flag Mahler construction uses the finite types property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L302-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L302-L318

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

theorem GlobalTheory.FlagMahler.finite_types {ι : Type} [Fintype ι] [DecidableEq ι] (C D : ℝ) (hD : 0 ≤ D) :
    (HermitianLatticeMaps.ty X '' {f : Basis ι ℤ X.Λ | ∃ y, IntegralBasisReduction.IsNormal X y ∧
      (∀ i, QuadraticLatticeForms.Qy X y (f i) ≤ C) ∧
      ∀ (v : X.Λ) (i : ι), ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ D * QuadraticLatticeForms.Qy X y v}).Finite := by sorry
