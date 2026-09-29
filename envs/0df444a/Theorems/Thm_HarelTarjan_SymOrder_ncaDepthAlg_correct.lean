-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_ncaDepthAlg_correct
-- name    : HarelTarjan.SymOrder.ncaDepthAlg_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:48:37.018298+00:00
-- url     : https://prove2.me/theorems/ea52ab1e-3530-4179-8a24-f6385b8dfe90
-- title:
--   The nca depth algorithm returns the depth of $\operatorname{nca}(v,w)$
-- statement:
--   Let $T$ be the complete binary tree of depth $d$, numbered in symmetric order. For all vertices $v, w$ of $T$, the algorithm to solve the nca depth problem of §3 (p. 342) returns the depth of their nearest common ancestor:
--   $$\mathrm{ncaDepth}(v,w) = \operatorname{depth}(\operatorname{nca}(v,w)).$$
--   Here $\mathrm{ncaDepth}(v,w)$ is $d - h(v)$ if $\mathrm{sym}(w) \in [\mathrm{sym}(v) - 2^{h(v)} + 1, \mathrm{sym}(v) + 2^{h(v)} - 1]$; otherwise $d - h(w)$ if $\mathrm{sym}(v) \in [\mathrm{sym}(w) - 2^{h(w)} + 1, \mathrm{sym}(w) + 2^{h(w)} - 1]$; otherwise $d - \lfloor \lg(\mathrm{sym}(v) \oplus \mathrm{sym}(w)) \rfloor$.
--
--   This is Step 1 of the algorithm to compute $\operatorname{nca}(v,w)$; the paper derives it from Lemmas 2 and 4.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, §3, Algorithm to solve the nca depth problem (unnumbered)

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Definitions.Def_HarelTarjan_SymOrder_Algorithms

namespace HarelTarjan.SymOrder

/-- The algorithm to solve the nca depth problem (§3, p. 342) is correct: for all vertices `v`,
`w`, it returns the depth of the nearest common ancestor of `v` and `w`. -/
theorem ncaDepthAlg_correct {d : ℕ} (v w : Vertex d) :
    ncaDepthAlg v w = depth (nca v w) := by sorry

end HarelTarjan.SymOrder
