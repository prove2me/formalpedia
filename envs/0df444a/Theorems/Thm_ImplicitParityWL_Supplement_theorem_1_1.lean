-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_1_1
-- name    : ImplicitParityWL.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:28:14.477062+00:00
-- url     : https://prove2.me/theorems/5ae061b6-4f9a-456d-af7d-c06e6dd3f62b
-- title:
--   Theorem 1.1 — no multitape TM solves $k$-WL Distinguishing in time $O(n^{k-1-\varepsilon})$
-- statement:
--   For every fixed $k\ge3$ and $\varepsilon>0$, no deterministic multitape Turing machine solves $k$-WL Distinguishing in time $O(n^{k-1-\varepsilon})$. Here an instance is a pair of graphs $G,H$, the question is whether $k$-WL distinguishes them (some color of $k$-tuples occurs a different number of times in $G$ and in $H$), and $n=|V(G)|+|V(H)|$.
--
--   Precisely: there is no machine $M$ and no constant $C$ such that, for all uncolored graphs $G,H$, on the input consisting of the edge-list codes of $G$ and $H$ the machine $M$ halts within
--   $$\bigl\lfloor C\,(n+1)^{k-1-\varepsilon}\bigr\rfloor$$
--   steps with output $1$ if $k$-WL distinguishes $G$ and $H$ and $0$ otherwise.
--
--   The bound nearly matches the $O(n^{k+1}\log n)$ algorithm, and it is unconditional.
--
--   **Formalization Note** The machine model is the published `OAI.VariableWL.Machine`, and $k$-WL is the published `OAI.VariableWL.Equivalent`. The machine need only be correct and fast on well-formed codes.
--
--   Differences from the source:
--   - reading: k-WL Distinguishing on graphs → uncolored graphs (OAI.VariableWL.Graph); reason: the stronger reading; the proof's colored pairs are made uncolored by footnote 3, as for the published goal
--   - encoding: input format not fixed → edgeCode G ++ edgeCode H (order, edge count, sorted edge list); reason: an edge list of length O((n+m) log n), so the time bound in n is not trivialized by an n²-bit input
--   - generalization: a machine that solves the problem on every input → correct output and halting bound required only on well-formed codes; reason: a machine deciding the language on all words satisfies the promise version, so the Lean lower bound implies the source's
--   - encoding: time O(n^(k−1−ε)) → halting within ⌊C·(n+1)^(k−1−ε)⌋₊ steps for one real C, n = G.order + H.order; reason: the +1 avoids 0 to a real power; finitely many small instances are absorbed in C
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 1.1, p.2 (restated p.52)

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_ImplicitParityWL_Supplement_Codes

namespace ImplicitParityWL

namespace Supplement

open OAI.VariableWL

/-- **Theorem 1.1** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman
Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.2, restated p.52): for every
fixed `k ≥ 3` and `ε > 0`, no deterministic multi-tape Turing machine solves `k`-WL Distinguishing in
time `O(n^{k-1-ε})`.

**Formalization Note** The machine is the published `OAI.VariableWL.Machine` (deterministic, several
tapes, input and output as bit words on tape `0`). An instance is a pair of uncolored graphs given as
`edgeCode G ++ edgeCode H` (order, edge count, edge list); the answer is `true` iff `k`-WL distinguishes
`G` and `H` (some round's histograms differ). `n` is the total number of vertices `G.order + H.order`,
and "time `O(n^{k-1-ε})`" is a halting bound `⌊C·(n + 1)^{k-1-ε}⌋` for one real `C`, finitely many small
instances being absorbed in `C`. The machine is only required to be correct on well-formed codes. -/
theorem theorem_1_1 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ (M : Machine) (C : ℝ), ∀ G H : Graph, ∃ b : Bool, (b = true ↔ ¬ Equivalent G H k) ∧
      OutputsWithin M (edgeCode G ++ edgeCode H) [b]
        ⌊C * ((G.order + H.order : ℕ) + 1 : ℝ) ^ ((k : ℝ) - 1 - ε)⌋₊ := by sorry

end Supplement

end ImplicitParityWL
