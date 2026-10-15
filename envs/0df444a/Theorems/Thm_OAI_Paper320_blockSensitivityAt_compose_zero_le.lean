-- Prove2me | Theorems.Thm_OAI_Paper320_blockSensitivityAt_compose_zero_le
-- name    : OAI.Paper320.blockSensitivityAt_compose_zero_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:12:03.842983+00:00
-- url     : https://prove2.me/theorems/c4e67156-2abb-4423-83c2-de83cec2db62
-- title:
--   Block sensitivity at the zero input is supermultiplicative under composition
-- statement:
--   Let $I$ and $J$ be finite sets and identify Boolean values with $\{0,1\}$. For Boolean functions $f : \{0,1\}^I \to \{0,1\}$ and $g : \{0,1\}^J \to \{0,1\}$, their block composition is the function on $\{0,1\}^{I \times J}$ given by
--   $(f \circ g)(x) = f\big((g(x_{i,\cdot}))_{i \in I}\big)$, where $x_{i,\cdot} = (x_{(i,j)})_{j \in J}$ is the block of coordinates read by the $i$-th copy of $g$. Write $\mathbf{0}$ for the all-zero input (in any dimension), $x^{B}$ for $x$ with the coordinates in $B$ flipped, and $\mathrm{bs}(h, \mathbf{0})$ for the block sensitivity of $h$ at $\mathbf{0}$: the largest number of pairwise disjoint nonempty coordinate sets $B$ such that $h(\mathbf{0}^{B}) \ne h(\mathbf{0})$.
--
--   If $g(\mathbf{0}) = 0$, then
--
--   $$
--   \mathrm{bs}(f, \mathbf{0}) \cdot \mathrm{bs}(g, \mathbf{0}) \le \mathrm{bs}(f \circ g, \mathbf{0}).
--   $$
--
--   No assumption is made on $f$. Together with the elementary bound $\mathrm{bs}(\mathrm{OR}_K, \mathbf{0}) \ge |K|$, this shows that taking the OR of $|K|$ disjoint copies of a function vanishing at $\mathbf{0}$ multiplies its block sensitivity at $\mathbf{0}$ by at least $|K|$, which is how block sensitivity is amplified in constructions separating block sensitivity from sensitivity.
--
--   **Formalization Note** Boolean values are `Bool`, with `false` playing the role of $0$; the composition is `compose f g`, and `blockSensitivityAt h x` is defined as a maximum over finite families of finite coordinate sets that are pairwise disjoint, nonempty and change the value of `h` when flipped at `x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Composition.lean#L106-L137

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition

open OAI OAI.Paper320
open scoped Classical BigOperators
variable {I J : Type}
variable [Fintype I] [Fintype J]

theorem OAI.Paper320.blockSensitivityAt_compose_zero_le (f : (I → Bool) → Bool)
    (g : (J → Bool) → Bool) (hg : g (fun _ => false) = false) :
    blockSensitivityAt f (fun _ => false) * blockSensitivityAt g (fun _ => false) ≤
      blockSensitivityAt (compose f g) (fun _ => false) := by sorry
