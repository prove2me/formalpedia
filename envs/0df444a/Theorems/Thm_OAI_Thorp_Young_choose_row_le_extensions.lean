-- Prove2me | Theorems.Thm_OAI_Thorp_Young_choose_row_le_extensions
-- name    : OAI.Thorp.Young.choose_row_le_extensions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:29:57.08906+00:00
-- url     : https://prove2.me/theorems/f170d88a-11d2-4e69-99f0-dfcf9e0ea9a6
-- title:
--   First-row binomial lower bound $\binom{\lambda_1}{u}$ for the number of standard Young tableaux
-- statement:
--   Let $D$ be a Young diagram: a finite set of cells $(r,c)\in\mathbb{N}^2$ ($r$ the row index, $c$ the column index, row $0$ being the first row) that is closed downward, i.e. $(r',c')\le(r,c)$ componentwise and $(r,c)\in D$ imply $(r',c')\in D$. Order the cells of $D$ componentwise. A linear extension of this cell poset, i.e. a bijection $D\to\{0,\dots,|D|-1\}$ that increases strictly along rows and down columns, is the same thing as a standard Young tableau of shape $D$; write $f^D$ for their number. Let $\lambda_1$ be the number of cells in the first row of $D$ and $u$ the number of cells of $D$ outside the first row. If $u\le\lambda_1$, then
--
--   $$
--   \binom{\lambda_1}{u}\le f^D.
--   $$
--
--   This is a lower bound for the number of standard Young tableaux, and hence for the dimension of the corresponding irreducible representation of the symmetric group, in terms of the length of the first row and the size of the rest of the diagram. After trimming the part below the first row to $k$ cells it gives $\binom{\lambda_1}{k}\le f^D$ for every $k\le\min(u,\lambda_1)$, which is how it is used for diagrams with a long first row.
--
--   **Formalization Note** $D$ is a Mathlib `YoungDiagram`, the cells are the subtype `Cells D` with the order inherited from `ℕ × ℕ`, $f^D$ is `Fintype.card (Extensions (Cells D))`, $\lambda_1$ is `D.rowLen 0`, and $u$ is the cardinality of `Lower D`, the cells with nonzero row index.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean#L192-L231

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

open OAI OAI.Thorp OAI.Thorp.Young
universe uA
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical

theorem OAI.Thorp.Young.choose_row_le_extensions (D : YoungDiagram)
    (hu : Fintype.card (Lower D) ≤ D.rowLen 0) :
    (D.rowLen 0).choose (Fintype.card (Lower D)) ≤ Fintype.card (Extensions (Cells D)) := by sorry
