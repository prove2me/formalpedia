-- Prove2me | Theorems.Thm_GlobalTheory_Published_Landherr_congr_of_gram_eq
-- name    : GlobalTheory.Published.Landherr.congr_of_gram_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:21.407829+00:00
-- url     : https://prove2.me/theorems/5ffc46bf-b9ca-4513-b7cc-f5bd83876067
-- title:
--   Landherr: congr of gram eq
-- statement:
--   The Landherr construction uses the congr of gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L127-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L127-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.Published.Landherr.congr_of_gram_eq (τ : E →+* ℂ) {Q Q' : Matrix (Fin r) (Fin r) ℂ} (hQ : Q.det ≠ 0)
    (hQ' : Q'.det ≠ 0) (h : gram τ G Q = gram τ G' Q') :
    ∃ R : Matrix (Fin r) (Fin r) ℂ, R.det ≠ 0 ∧ G'.map τ = Rᵀ * G.map τ * R.map conj := by sorry
