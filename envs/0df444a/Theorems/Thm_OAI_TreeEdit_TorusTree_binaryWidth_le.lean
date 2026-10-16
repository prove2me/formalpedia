-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_binaryWidth_le
-- name    : OAI.TreeEdit.TorusTree.binaryWidth_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:16:27.28595+00:00
-- url     : https://prove2.me/theorems/5246400d-b98d-4667-8e71-2f8fd0de4c05
-- title:
--   The binary code width is at most $40k^2$
-- statement:
--   For an integer $k\ge 2$ let $m=16k^3$ and $R=k^{8k}$, and let $m^kR=(16k^3)^k\,k^{8k}$ be the size of the alphabet of the depth-$k$ circle-tree words. For a positive integer $n$ let $\lceil\log_2 n\rceil$ denote the least integer $e\ge 0$ with $n\le 2^e$. The binary width is $B_k=2\lceil\log_2(m^kR)\rceil+3$, and it satisfies
--   $$
--   B_k=2\Big\lceil\log_2\big((16k^3)^k\,k^{8k}\big)\Big\rceil+3\le 40\,k^2\qquad\text{for all integers }k\ge 2.
--   $$
--
--   The number $B_k$ is the length of the binary codeword that the synchronizing delimiter code assigns to each letter of an alphabet of size $m^kR$. The quadratic bound controls both the length blow-up of the binary encoding and the loss factor in the final $\ell_1$-distortion bound, and it enters the estimate $\log(\text{string length})\le 60k^2\log k$.
--
--   **Formalization Note** In Lean, $B_k$ is `binaryWidth k = 2*Nat.clog 2 (alphabetSize k)+3` with `alphabetSize k = branching k^k * resolution k` and `branching k = 16*k*k^2`; `Nat.clog 2 n` is the ceiling base-2 logarithm described above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleParameters.lean#L26-L45

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters

open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

theorem OAI.TreeEdit.TorusTree.binaryWidth_le {k : ℕ} (hk : 2 ≤ k) : binaryWidth k ≤ 40*k^2 := by sorry
