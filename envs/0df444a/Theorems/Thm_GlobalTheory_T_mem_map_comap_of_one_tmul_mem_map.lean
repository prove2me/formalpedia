-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_map_comap_of_one_tmul_mem_map
-- name    : GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:16.112807+00:00
-- url     : https://prove2.me/theorems/bc011ab1-7f1f-545a-abd8-14487eacac09
-- title:
--   T: mem map comap of one tmul mem map
-- statement:
--   The T construction uses the mem map comap of one tmul mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatComapMapOfOneTmulMemStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatComapMapOfOneTmulMemStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatComapMapOfOneTmulMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatComapMapOfOneTmulMemStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map : ∀ {B C R : Type} [CommRing B] [CommRing C] [CommRing R] [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R), (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) → r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by sorry
