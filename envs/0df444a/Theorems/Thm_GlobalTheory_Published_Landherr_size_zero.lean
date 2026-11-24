-- Prove2me | Theorems.Thm_GlobalTheory_Published_Landherr_size_zero
-- name    : GlobalTheory.Published.Landherr.size_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:24.023448+00:00
-- url     : https://prove2.me/theorems/0b2b4333-300e-4718-a2df-64a704015fea
-- title:
--   Landherr: size zero
-- statement:
--   The Landherr construction uses the size zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L103-L105

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

theorem GlobalTheory.Published.Landherr.size_zero (G G' : Matrix (Fin 0) (Fin 0) E) :
    ∃ P : Matrix (Fin 0) (Fin 0) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by sorry
