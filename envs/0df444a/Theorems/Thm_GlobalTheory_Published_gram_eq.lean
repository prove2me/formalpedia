-- Prove2me | Theorems.Thm_GlobalTheory_Published_gram_eq
-- name    : GlobalTheory.Published.gram_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:45.307179+00:00
-- url     : https://prove2.me/theorems/fa7b2607-db81-4fc3-bf24-b3b9c56dc8dd
-- title:
--   Published: gram eq
-- statement:
--   The Published construction uses the gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L40-L45

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.Published.gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Q = Qᵀ * G.map τ * Q.map conj := by sorry
