-- Prove2me | Theorems.Thm_OAI_Thorp_Specht_defect_card_bound
-- name    : OAI.Thorp.Specht.defect_card_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:36:51.716932+00:00
-- url     : https://prove2.me/theorems/3ae470c0-4ca5-4f68-96ec-a5b20450bfda
-- title:
--   At most $2^{u+1}$ partitions of $n$ have defect $u$
-- statement:
--   Let $\lambda=(\lambda_1\ge\lambda_2\ge\dots\ge\lambda_\ell>0)$ be a partition of $n$ with $\ell=\ell(\lambda)$ parts, and let $D_\lambda$ be its Young diagram (row $r$ consists of the cells $(r,0),\dots,(r,\lambda_{r+1}-1)$). The longest line of the diagram has length $L(\lambda)=\max(\lambda_1,\ell(\lambda))$, the larger of the first-row length and the first-column length, and the *defect* of $\lambda$ is
--   $$\operatorname{def}(\lambda)=n-L(\lambda),$$
--   the number of cells outside the longer of the first row and the first column.
--
--   For all natural numbers $n$ and $u$,
--
--   $$
--   \#\{\lambda\vdash n:\ \operatorname{def}(\lambda)=u\}\le 2^{u+1}.
--   $$
--
--   The bound is independent of $n$: a partition with small defect is a long first row or first column plus a small partition attached to it. In sums over the irreducible representations of $S_n$, such as $\sum_\lambda 1/\dim S^\lambda$, this controls the number of shapes in each defect slice, which is then combined with lower bounds on $\dim S^\lambda$ that grow exponentially in the defect.
--
--   **Formalization Note** The set is the subtype `{p : NShape n // defect p = u}` of partitions of `Fintype.card (Fin n)` (which is $n$), and `defect p = n - longest (ofPartition p)` with `longest D = max (D.rowLen 0) (D.colLen 0)`. When $u>n$ the set is empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/DegreeBounds.lean#L219-L232

import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds

open OAI OAI.Thorp OAI.Thorp.Specht
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical
open Thorp.Young

theorem OAI.Thorp.Specht.defect_card_bound (n u : ℕ) :
    Fintype.card {p : NShape n // defect p = u} ≤ 2 ^ (u + 1) := by sorry
