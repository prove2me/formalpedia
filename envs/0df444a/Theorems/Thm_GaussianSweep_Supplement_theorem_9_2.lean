-- Prove2me | Theorems.Thm_GaussianSweep_Supplement_theorem_9_2
-- name    : GaussianSweep.Supplement.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:42:47.358527+00:00
-- url     : https://prove2.me/theorems/01d9b4da-0af2-4006-811a-4de7b85df9ce
-- title:
--   Theorem 9.2 — the tuples C, M, F, S, P, R are pathwidth sequences
-- statement:
--   Each of the following six tuples is a pathwidth sequence (Definition 9.1), that is, after continuing it with coefficient $1$ for every larger degree, it bounds the pathwidth of every finite simple graph up to $o(n)$:
--   $$
--   C = (c_3),\quad M = (c_3, 0.2627),\quad F = (F_4, F_4),\quad S = \big(\tfrac{5}{32}, \tfrac14, \tfrac{11}{32}\big),
--   $$
--   $$
--   P = (F_3, 0.2575, 0.3667),\quad R = (0.1455, 0.2530, 0.3600).
--   $$
--   For instance $C$ says $\mathrm{pw}(G) \le c_3 n_3 + \sum_{d > 3} n_d + o(n)$ for every graph, with no degree bound.
--
--   Differences from the source:
--   - encoding: a finite tuple (a3, …, ak) → tupleSeq [a3, …, ak], the sequence continued by 1 for d > k; reason: Definition 9.1's own convention for finite tuples
--   - encoding: 'each of the six tuples' is a pathwidth sequence → a conjunction of six IsPathwidthSeq statements, each with its own remainder; reason: Definition 9.1 attaches one o(n) function to each sequence
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 9.2, p.56 (PDF p.58); Definition 9.1, p.56 (PDF p.58)

import Mathlib
import Definitions.Def_GaussianSweep_c3
import Definitions.Def_GaussianSweep_Supplement_F3
import Definitions.Def_GaussianSweep_Supplement_F4__069df8
import Definitions.Def_GaussianSweep_Supplement_tupleSeq
import Definitions.Def_GaussianSweep_Supplement_IsPathwidthSeq

namespace GaussianSweep.Supplement

/-- Theorem 9.2 (pathwidth sequences) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 9.2, p.56 (PDF p.58)).
Each of the following six tuples is a pathwidth sequence (Definition 9.1):
`C = (c₃)`, `M = (c₃, 0.2627)`, `F = (F₄, F₄)`, `S = (5/32, 1/4, 11/32)`,
`P = (F₃, 0.2575, 0.3667)`, `R = (0.1455, 0.2530, 0.3600)`.

**Formalization Note** A finite tuple stands for the sequence continued by `1` (`tupleSeq`), and
a pathwidth sequence bounds the pathwidth of every graph, with no degree bound
(`IsPathwidthSeq`); so `C` is not Theorem 8.1 but the bound
`pw(G) ≤ c₃ n₃ + Σ_{d>3} n_d + o(n)` for all graphs. Each tuple has its own remainder. -/
theorem theorem_9_2 :
    IsPathwidthSeq (tupleSeq [GaussianSweep.c3]) ∧
    IsPathwidthSeq (tupleSeq [GaussianSweep.c3, 0.2627]) ∧
    IsPathwidthSeq (tupleSeq [F4, F4]) ∧
    IsPathwidthSeq (tupleSeq [5 / 32, 1 / 4, 11 / 32]) ∧
    IsPathwidthSeq (tupleSeq [F3, 0.2575, 0.3667]) ∧
    IsPathwidthSeq (tupleSeq [0.1455, 0.2530, 0.3600]) := by sorry

end GaussianSweep.Supplement
