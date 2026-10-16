-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_deterministic_rate
-- name    : OAI.TwoWayComplementation.deterministic_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:02:55.584997+00:00
-- url     : https://prove2.me/theorems/ebcb64e2-43d0-4e8e-abfe-418998141b66
-- title:
--   Converting the bound $2^{\lfloor (n-4)/31\rfloor}\le 4(s+1)^2$ into $s\ge\frac12\cdot 2^{\lfloor (n-4)/127\rfloor}$
-- statement:
--   Let $n$ and $s$ be natural numbers with $n\ge 131$, and write $\lfloor x\rfloor$ for the integer part of a real number $x\ge0$. If
--
--   $$
--   2^{\lfloor (n-4)/31\rfloor}\le 4\,(s+1)^2,
--   $$
--
--   then
--
--   $$
--   \frac12\cdot 2^{\lfloor (n-4)/127\rfloor}\le s .
--   $$
--
--   This is a purely arithmetic conversion between two exponential scales. For two-way automata over the alphabet of all binary relations on $h=n-2$ points, a two-way deterministic automaton with $s$ states that accepts exactly the words whose relational product is nonempty, under the acceptance convention that allows runs of length zero, satisfies a bound of the form $2^{\lfloor (h-2)/31\rfloor}\le 4(s+1)^2$, and $h-2=n-4$. The lemma turns this bound on $(s+1)^2$ into a lower bound on $s$ itself, on the same scale $2^{\lfloor (n-4)/127\rfloor}$ as the lower bound for complementing $n$-state two-way nondeterministic automata, so that both bounds can be stated for one family of automata. The slower rate $1/127$ in place of $1/31$ is what absorbs the square, since $4\cdot 31\le 127$.
--
--   **Formalization Note** Here `n - 4` is natural-number subtraction (it does not truncate because $n\ge131$) and `/` is natural-number division, i.e. the floor. The hypothesis is an inequality between natural numbers and the conclusion an inequality between real numbers, so $\frac12\cdot 2^{\lfloor (n-4)/127\rfloor}$ is not rounded.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/DeterministicBound.lean#L28-L51

import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_TransitionBridge

open OAI OAI.TwoWayComplementation

theorem OAI.TwoWayComplementation.deterministic_rate (n s : ℕ) (hn : 131 ≤ n)
    (hb : 2 ^ ((n - 4) / 31) ≤ 4 * (s + 1) ^ 2) :
    (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (s : ℝ) := by sorry
