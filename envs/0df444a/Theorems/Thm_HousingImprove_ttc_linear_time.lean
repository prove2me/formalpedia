-- Prove2me | Theorems.Thm_HousingImprove_ttc_linear_time
-- name    : HousingImprove.ttc_linear_time
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:11.905992+00:00
-- url     : https://prove2.me/theorems/6df4b6f8-90f7-4352-9584-a712db2b0779
-- title:
--   TTC for partial orders runs in $O(|H|)$ time
-- statement:
--   There is a constant $C$ such that, for every housing market $H$ on the agents $\{0,\dots,n-1\}$ presented by its Hasse diagrams $I$ and every set $W$ of agents, the program `ttcProg` run on $W$ performs at most
--   $$C\cdot(|H|+1)$$
--   unit operations, where $|H|=\sum_a|H_a|$ counts the vertices and arcs of the Hasse diagrams.
--
--   Since $|H|\ge|N|$, this is the bound $O(|N|+\sum_{a\in N}|H_a|)=O(|H|)$ of the paper.
--
--   Differences from the source:
--   - reading: |H| (not defined in Theorem 2) → HassePres.size: Σ_a (vertices + arcs of the Hasse diagram H_a); reason: Appendix A, p.30 defines |H| = Σ_a |H_a|; |H_a| counts vertices and arcs, as the bound O(|N| + Σ_a |H_a|) = O(|H|) on p.30 needs
--   - reading: O(|H|) time → one universal constant C, placed before the instance, bounding the number of unit operations of the concrete charged program; reason: unit-cost RAM; the program is a specific definition under the charging discipline of Prog, so the bound cannot be met by a cost-free Lean function
--   - encoding: given H, H′ and X (and p) → Hasse-diagram presentations I of H and I′ of H′ (vertex, out- and in-neighbour lists), X as a function, p; reason: the input format of Appendix A, p.30; Represents ties each presentation to its market
--   - reading: O(|N| + Σ_{a∈N} |H_a|) = O(|H|) → C · (|H| + 1); reason: for n ≥ 1, |H| ≥ n ≥ 1 and C · (|H| + 1) ≤ 2C · |H|; the + 1 only covers the market with no agents, on which any program performs a step
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Appendix A, p.30 ("the total running time of our variant of TTC is O(|N| + Σa∈N |Ha|) = O(|H|)")

import Mathlib
import Definitions.Def_HousingImprove_ttcProg

namespace HousingImprove

/-- **TTC for partial orders runs in linear time** (Schlotter, Biró, Fleiner, arXiv:2110.06875v3,
Appendix A, p.30): "Using the data structures described above the total running time of our
variant of TTC is `O(|N| + Σ_{a∈N} |H_a|) = O(|H|)`."

There is a universal constant `C` such that for every market `H` on `Fin n` presented by `I` and
every agent set `W`, the program `ttcProg` run on `W` performs at most `C · (|H| + 1)` unit
operations.

**Formalization Note.** `|H|` is `HassePres.size` (vertices plus arcs of the Hasse diagrams), and
`|H| ≥ |N|`. The `+ 1` matters only when there are no agents (`n = 0`, `|H| = 0`); for `n ≥ 1`,
`|H| ≥ 1`. `ttcProg` is one concrete program under the charging discipline of `Prog`; `W` may be
empty. Its correctness is `ttc_core`. -/
theorem ttc_linear_time :
    ∃ C : ℕ, ∀ (n : ℕ) (H : Market (Fin n)) (I : HassePres n) (W : Finset (Fin n)),
      Represents I H →
      ((ttcProg I fun b => decide (b ∈ W)).run 0).2 ≤ C * (I.size + 1) := by sorry

end HousingImprove
