-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cliqueMinorFree_iff_not_isMinor
-- name    : LeanPool.K5MinorFreeChoosability.cliqueMinorFree_iff_not_isMinor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:21.6426+00:00
-- url     : https://prove2.me/theorems/860dc0c3-8d67-5afd-b441-1ccd8d6d1d2e
-- title:
--   K5 Minor Free Choosability: clique Minor Free iff not is Minor
-- statement:
--   The K5 Minor Free Choosability construction uses the clique Minor Free iff not is Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L72-L74
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L72-L74

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
variable {G : SimpleGraph V} {k : ℕ}

theorem LeanPool.K5MinorFreeChoosability.cliqueMinorFree_iff_not_isMinor :
    CliqueMinorFree G k ↔ ¬ IsMinor (⊤ : SimpleGraph (Fin k)) G := by sorry
