-- Prove2me | Theorems.Thm_Freiman_trunkFast_correctness
-- name    : Freiman.trunkFast_correctness
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T10:07:40.546634+00:00
-- url     : https://prove2.me/theorems/bfd28675-3711-4ef0-ac89-bc5216b85285
-- title:
--   Soundness of fast Freiman trunk certificate checking
-- statement:
--   Two reusable facts justify the fast certificate interface. First, when distinct raw parent entries have different underlying finite sets of bounds, the catalog’s deduplication procedure returns exactly that raw list. Second, for any of the sixteen trunk states whose raw and deduplicated parent lists agree, every group satisfying the fast finite predicate satisfies the original catalog predicate. The proof establishes lookup equivalence for concatenated arrays, proves leaf and tree correspondence, and transfers every group condition. No particular row or theorem instance is assumed.
-- source:
--   Freiman Hall ray report, Section 15, trunk certificate and Proposition 4.1. The symbolic array-chain lookup and mirror-predicate proof architecture are adapted with attribution from Marac’s accepted public submission https://prove2.me/submissions/93a6c511-3ed0-48c3-bbd0-ecae49532be4; this reusable interface generalizes the group correspondence from a single state to every state under an explicit raw-parent equality hypothesis.

import Definitions.Def_Freiman_trunkFast
open Freiman Freiman.TrunkFast

theorem Freiman.trunkFast_correctness :
    (∀ C : LowerHistoryContext,
      (trunkRawParents C).Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset) →
      trunkParents C = trunkRawParents C) ∧
    (∀ k : Fin 16,
      trunkParents (trunkCatalog.states k).context = trunkRawParents (trunkCatalog.states k).context →
      ∀ g : TrunkGroup, trunkGroupValidFast k g → trunkGroupValid trunkCatalog k g) := by
  sorry
