-- Prove2me | Theorems.Thm_OAI_TreeEdit_sqrt_log_cap
-- name    : OAI.TreeEdit.sqrt_log_cap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:20:17.005609+00:00
-- url     : https://prove2.me/theorems/e06cded0-c5c2-4098-98f3-83c7b55fced6
-- title:
--   Inverting the length cap: $\sqrt{\log d\,\log\log d}\le 8A\,k\log k$
-- statement:
--   Let $A,k,d$ be real numbers with $A\ge 1$, $k\ge 8A$ and $d>1$, and let $\log$ denote the natural logarithm. If
--   $$
--   \log d\le A\,(k+1)^2\log(k+1),
--   $$
--   then
--   $$
--   \sqrt{\log d\cdot\log\log d}\le 8A\,k\log k.
--   $$
--
--   In the final step of the edit-distance lower bound, a scale $k$ is chosen so that the witness length $N(k)$ satisfies $N(k)\le d<N(k+1)$, where $\log N(k)\le A\,k^2\log k$. This lemma converts the per-scale lower bound $\exp(k\log k/2)$ into the bound $\exp\big(c\sqrt{\log d\,\log\log d}\big)$ with $c=1/(16A)$, expressed in terms of the length cap $d$.
--
--   **Formalization Note** Lean's `Real.sqrt` returns $0$ on negative inputs. When $1<d<e$ one has $\log\log d<0$, so the left-hand side is $0$ and the inequality holds trivially.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CapInversion.lean#L11-L54

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
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer

open OAI OAI.TreeEdit
universe u
attribute [local instance] Classical.propDecidable

theorem OAI.TreeEdit.sqrt_log_cap {A k d : ℝ} (hA : 1 ≤ A) (hk : 8 * A ≤ k) (hd : 1 < d)
    (hcap : Real.log d ≤ A * (k + 1) ^ 2 * Real.log (k + 1)) :
    Real.sqrt (Real.log d * Real.log (Real.log d)) ≤ 8 * A * (k * Real.log k) := by sorry
