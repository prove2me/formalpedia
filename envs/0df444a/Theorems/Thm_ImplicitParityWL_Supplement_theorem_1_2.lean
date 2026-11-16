-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_1_2
-- name    : ImplicitParityWL.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:28:48.806922+00:00
-- url     : https://prove2.me/theorems/e417e9d6-2c71-4dcd-8f03-610b8db8e82b
-- title:
--   Theorem 1.2 — WL Distinguishing is EXPTIME-complete, and XP-complete parameterized by $k$
-- statement:
--   The problem WL Distinguishing, which asks for uncolored graphs $G,H$ and an integer $k\ge2$ given in the input whether $k$-WL distinguishes $G$ and $H$, satisfies:
--
--   1. it is **EXPTIME-complete**: it is decided in time $2^{\mathrm{poly}(|w|)}$, and every language in EXPTIME reduces to it by a polynomial-time many-one reduction;
--   2. parameterized by $k$, it is **XP-complete**: it is in XP, and every parameterized problem in XP reduces to it by an fpt-reduction.
--
--   This settles the classical and the parameterized complexity of WL Distinguishing; before, the problem was known to be NP-hard and even W[1]-hardness was open.
--
--   **Formalization Note** The instances are the published `pairCode` words (adjacency matrices, $k$ in a self-delimiting binary code). EXPTIME-completeness is the published `OAI.VariableWL.EXPTIMEComplete`; XP, parameterizations and fpt-reductions are those of the definition `ImplicitParityWL.Supplement.Complexity` (Flum–Grohe).
--
--   Differences from the source:
--   - reading: WL Distinguishing on graphs → uncolored graphs (OAI.VariableWL.Graph); reason: the stronger reading; the hardness proofs remove the colors of the compiled pairs by footnote 3
--   - reading: dimension k part of the input → instances with k ≥ 2; reason: folklore k-WL is used for k ≥ 2 (p.2), as in the published language OAI.VariableWL.WL
--   - encoding: input format not fixed → pairCode G H k (adjacency matrices, k as integerCode); reason: the published encoding of the same problem
--   - encoding: EXPTIME, XP, fpt-reductions (not defined in the paper) → published EXPTIMEComplete; XP and fpt-reductions per Flum–Grohe with computable f, g and polynomial-time parameterizations; reason: the standard notions the paper refers to
--   - encoding: parameterization by k → κ(pairCode G H k) = k, κ = 0 on other words; reason: a parameterization must be total on words
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 1.2, p.2 (restated p.50)

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_ImplicitParityWL_Supplement_Complexity

namespace ImplicitParityWL

namespace Supplement

open OAI.VariableWL

/-- **Theorem 1.2** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman
Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.2, restated p.50): the problem
WL Distinguishing is EXPTIME-complete when the dimension `k` is part of the input. It is XP-complete
when parameterized by `k`.

**Formalization Note** WL Distinguishing is `WLDist`: codes `pairCode G H k` of two uncolored graphs and
`k ≥ 2` such that `k`-WL distinguishes `G` and `H`. EXPTIME-completeness is the published
`OAI.VariableWL.EXPTIMEComplete` (membership and hardness under polynomial-time many-one reductions).
XP-completeness is `XPComplete` for the parameterization `wlParam` (`k` on pair codes): membership in XP
and hardness under fpt-reductions, per Flum–Grohe. -/
theorem theorem_1_2 : EXPTIMEComplete WLDist ∧ XPComplete WLDist wlParam := by sorry

end Supplement

end ImplicitParityWL
