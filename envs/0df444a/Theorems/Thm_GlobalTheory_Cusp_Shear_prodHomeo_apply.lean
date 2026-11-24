-- Prove2me | Theorems.Thm_GlobalTheory_Cusp_Shear_prodHomeo_apply
-- name    : GlobalTheory.Cusp.Shear.prodHomeo_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:06.559007+00:00
-- url     : https://prove2.me/theorems/2969f7a7-7030-4fc6-b696-4ab748fd6698
-- title:
--   Shear: prod Homeo apply
-- statement:
--   The Shear construction uses the prod Homeo apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdHomeoSymmApplySnd.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdHomeoSymmApplySnd.lean#L50-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdHomeoSymmApplySnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cusp GlobalTheory.Cusp.Shear
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N N' : Subgroup G}
  {V : Type} [AddCommGroup V] [TopologicalSpace V] {s : V → G} {π : N → V}

theorem GlobalTheory.Cusp.Shear.prodHomeo_apply (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (z : N' × V) :
    (prodHomeo hle hs hsc hπc hπmul hπs hker z : G) = z.1 * s z.2 := by sorry

attribute [defeq] GlobalTheory.Cusp.Shear.prodHomeo_apply
