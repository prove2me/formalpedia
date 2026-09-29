-- Prove2me | Theorems.Thm_Freiman_lowerHistory_witness_metadata_06
-- name    : Freiman.lowerHistory_witness_metadata_06
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T00:34:55.253662+00:00
-- url     : https://prove2.me/theorems/a549ae5d-4881-4c40-9263-6681b8793a9a
-- title:
--   Freiman H5: history witness bounds and rectangles, part 06
-- statement:
--   Each stored Bernstein witness has a lower bound, an upper bound and a rational rectangle. For part 6 of the existing history witness catalogue, projecting these three fields gives exactly the existing bound-ID table together with the rectangle-index list in the formal statement. Thus, for every entry, the projection is $(B_{\ell_i},B_{u_i},R_{r_i})$. The rectangle indices are zero-based. This identity supplies the original witness data to the row-2 source-case proof needed by the H5 exception anchor. It asserts only the identity of the stored data; numerical witness validity is provided by its separate existing theorem.
-- source:
--   Original project definitions lowerHistoryWitnesses01–06, lowerHistoryWitnessIds01–06 and lowerHistoryRectangles. Necessary data projection for Freiman.lower_h5_exception_anchor, https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_witness_metadata_06 : lowerHistoryWitnesses06.toList.map
    (fun w => (w.lowerBound, w.upperBound, w.rectangle)) =
  (lowerHistoryWitnessIds06.toList.zip ([7,1,2,4,5,6,7,6,7,1,2,4,5,6,7,6,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7] : List ℕ)).map
    (fun z => (lowerHistoryBound z.1.1, lowerHistoryBound z.1.2,
      lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by sorry
