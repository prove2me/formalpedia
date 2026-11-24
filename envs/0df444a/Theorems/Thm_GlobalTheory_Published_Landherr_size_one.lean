-- Prove2me | Theorems.Thm_GlobalTheory_Published_Landherr_size_one
-- name    : GlobalTheory.Published.Landherr.size_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:27.961457+00:00
-- url     : https://prove2.me/theorems/9575b1dc-a34c-4d3e-90d8-12053a0e30e7
-- title:
--   Landherr: size one
-- statement:
--   The Landherr construction uses the size one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L107-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L107-L123

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

theorem GlobalTheory.Published.Landherr.size_one (G G' : Matrix (Fin 1) (Fin 1) E) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (h : ∃ x : E, G.det / G'.det = x * cc x) :
    ∃ P : Matrix (Fin 1) (Fin 1) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by sorry
