-- Prove2me | Theorems.Thm_GlobalTheory_Cusp_Shear_prodHomeo_symm_apply_snd
-- name    : GlobalTheory.Cusp.Shear.prodHomeo_symm_apply_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:15.216802+00:00
-- url     : https://prove2.me/theorems/3878a120-80c1-4488-86d4-ed441841a1c4
-- title:
--   Shear: prod Homeo symm apply snd
-- statement:
--   The Shear construction uses the prod Homeo symm apply snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdHomeoSymmApplySnd.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdHomeoSymmApplySnd.lean#L60-L63

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

theorem GlobalTheory.Cusp.Shear.prodHomeo_symm_apply_snd (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s)
    (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
    (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (n : N) :
    ((prodHomeo hle hs hsc hπc hπmul hπs hker).symm n).2 = π n := by sorry

attribute [defeq] GlobalTheory.Cusp.Shear.prodHomeo_symm_apply_snd
