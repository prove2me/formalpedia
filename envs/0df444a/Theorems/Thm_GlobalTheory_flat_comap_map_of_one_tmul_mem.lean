-- Prove2me | Theorems.Thm_GlobalTheory_flat_comap_map_of_one_tmul_mem
-- name    : GlobalTheory.flat_comap_map_of_one_tmul_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:51:54.532835+00:00
-- url     : https://prove2.me/theorems/25ea3dda-c370-4c71-a183-64bc66e04f1d
-- title:
--   Global Theory: flat comap map of one tmul mem
-- statement:
--   The Global Theory construction uses the flat comap map of one tmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatComapMapOfOneTmulMem.lean#L6-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatComapMapOfOneTmulMem.lean#L6-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatComapMapOfOneTmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.flat_comap_map_of_one_tmul_mem {B C R : Type} [CommRing B] [CommRing C] [CommRing R]
    [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R)
    (h : (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R)) :
    r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by sorry
