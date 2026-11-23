-- Prove2me | Theorems.Thm_GlobalTheory_Published_herm_col
-- name    : GlobalTheory.Published.herm_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:26.709861+00:00
-- url     : https://prove2.me/theorems/3282e53a-34df-43bf-a846-033bc2830b4f
-- title:
--   Published: herm col
-- statement:
--   The Published construction uses the herm col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean#L33-L36

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

theorem GlobalTheory.Published.herm_col (G P : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    herm G (fun k => P k a) (fun k => P k b) = (Pᵀ * G * P.map cc) a b := by sorry
