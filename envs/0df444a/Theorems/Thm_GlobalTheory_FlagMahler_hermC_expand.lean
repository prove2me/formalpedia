-- Prove2me | Theorems.Thm_GlobalTheory_FlagMahler_hermC_expand
-- name    : GlobalTheory.FlagMahler.hermC_expand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:38.354697+00:00
-- url     : https://prove2.me/theorems/efc48bc2-8cff-59b0-9e41-0e6f6944c41c
-- title:
--   Flag Mahler: herm C expand
-- statement:
--   The Flag Mahler construction uses the herm C expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L28-L36

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

theorem GlobalTheory.FlagMahler.hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by sorry
