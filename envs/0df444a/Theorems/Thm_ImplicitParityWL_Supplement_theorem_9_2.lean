-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_9_2
-- name    : ImplicitParityWL.Supplement.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:31:37.696711+00:00
-- url     : https://prove2.me/theorems/a0aa0396-68db-4a30-a7f5-e405f164910c
-- title:
--   Theorem 9.2 — no multitape TM decides WL Distinguishing in time $O(2^{\varepsilon\sqrt N})$
-- statement:
--   There is a constant $\varepsilon>0$ such that no deterministic multitape Turing machine decides WL Distinguishing in time $O(2^{\varepsilon\sqrt N})$, where $N$ denotes the number of vertices of the input graphs.
--
--   Precisely: there is no machine $M$ and no constant $C$ such that, for all uncolored graphs $G,H$ and every $k\ge2$, on the code of $(G,H,k)$ the machine $M$ halts within
--   $$\bigl\lfloor C\cdot2^{\varepsilon\sqrt N}\bigr\rfloor,\qquad N=|V(G)|+|V(H)|,$$
--   steps with output $1$ if $k$-WL distinguishes $G$ and $H$ and $0$ otherwise.
--
--   The bound is unconditional and measured in the number of vertices, not in the input length.
--
--   **Formalization Note** Instances are the published `pairCode` words; the machine need only be correct and fast on well-formed codes with $k\ge2$.
--
--   Differences from the source:
--   - reading: WL Distinguishing on graphs → uncolored graphs (OAI.VariableWL.Graph); reason: the stronger reading; the proof's colored pairs are made uncolored by footnote 3
--   - encoding: input format not fixed → pairCode G H k (adjacency matrices, k as integerCode), k ≥ 2; reason: the published encoding of the same problem
--   - generalization: a machine that decides the language on every input → correct output and halting bound required only on well-formed codes; reason: a machine deciding the language satisfies the promise version, so the Lean lower bound implies the source's
--   - encoding: time O(2^(ε√N)) → halting within ⌊C·2^(ε√N)⌋₊ steps for one real C, N = G.order + H.order; reason: 2^(ε√N) ≥ 1, so finitely many small instances are absorbed in C
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 9.2, p.51

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_ImplicitParityWL_Supplement_Complexity

namespace ImplicitParityWL

namespace Supplement

open OAI.VariableWL

/-- **Theorem 9.2** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman
Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.51): there is a constant
`ε > 0` such that no deterministic multitape Turing machine decides WL Distinguishing in time
`O(2^{ε√N})`, where `N` denotes the number of vertices of the input graphs.

**Formalization Note** Instances are the published codes `pairCode G H k` of two uncolored graphs and a
dimension `k ≥ 2` (the instances of `WLDist`), and the answer is `true` iff `k`-WL distinguishes `G` and
`H`. `N = G.order + H.order`. "Time `O(2^{ε√N})`" is a halting bound `⌊C·2^{ε√N}⌋` for one real `C`. The
machine is only required to be correct on well-formed codes. -/
theorem theorem_9_2 : ∃ ε : ℝ, 0 < ε ∧
    ¬ ∃ (M : Machine) (C : ℝ), ∀ (G H : Graph) (k : ℕ), 2 ≤ k →
      ∃ b : Bool, (b = true ↔ ¬ Equivalent G H k) ∧
        OutputsWithin M (pairCode G H k) [b]
          ⌊C * (2 : ℝ) ^ (ε * Real.sqrt ((G.order + H.order : ℕ) : ℝ))⌋₊ := by sorry

end Supplement

end ImplicitParityWL
