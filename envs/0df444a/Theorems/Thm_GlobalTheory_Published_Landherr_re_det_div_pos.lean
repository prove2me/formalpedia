-- Prove2me | Theorems.Thm_GlobalTheory_Published_Landherr_re_det_div_pos
-- name    : GlobalTheory.Published.Landherr.re_det_div_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:46.992416+00:00
-- url     : https://prove2.me/theorems/56024c25-4072-423b-bcab-c534071fd0d8
-- title:
--   Landherr: re det div pos
-- statement:
--   The Landherr construction uses the re det div pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L197-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L197-L212

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

theorem GlobalTheory.Published.Landherr.re_det_div_pos (hd : G.det ≠ 0) (τ : E →+* ℂ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    0 < (τ (G.det / G'.det)).re := by sorry
