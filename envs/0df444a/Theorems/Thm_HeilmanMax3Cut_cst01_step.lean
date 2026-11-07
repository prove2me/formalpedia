-- Prove2me | Theorems.Thm_HeilmanMax3Cut_cst01_step
-- name    : HeilmanMax3Cut.cst01_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:24.90617+00:00
-- url     : https://prove2.me/theorems/fce4edf0-5dd6-498a-87a3-6eb5f603d052
-- title:
--   p.1, [CST01] sentence — weighted and unweighted MAX-3-CUT have the same hardness
-- statement:
--   For every real $r$, the following are equivalent:
--
--   1. for every $\varepsilon>0$ there are $c>0$ and $s$ with $s/c\le r+\varepsilon$ such that MAX-3-CUT on (polynomially) weighted graphs is $(c,s)$-hard;
--   2. for every $\varepsilon>0$ there are $c>0$ and $s$ with $s/c\le r+\varepsilon$ such that MAX-3-CUT on simple graphs is $(c,s)$-hard.
--
--   The paper attributes this to P. Crescenzi, R. Silvestri and L. Trevisan, *On weighted vs unweighted versions of combinatorial optimization problems*, Inform. Comput. 167 (2001) [CST01].
--
--   Differences from the source:
--   - reading: "the weighted and unweighted versions … have the same hardness of approximation" → equivalence of "NP-hard to approximate within r + ε for every ε > 0" for weighted and for simple graphs; reason: the sentence compares approximation thresholds; both directions are stated
--   - encoding: weighted version → ℕ-weighted multigraphs with weights in unary (Max3CutHard.MaxKCutHard); reason: the published weighted encoding; polynomially bounded weights are the setting of [CST01]
--   - encoding: NP-hard to approximate MAX-3-CUT within r + ε → ∃ c > 0, s with s/c ≤ r + ε and (c, s)-gap NP-hardness, both promise sets restricted to graphs with at least one edge (MaxKCutHard 3 and MaxKCutHardSimple 3); reason: (c, s)-hardness is the form the reductions produce, and it implies NP-hardness of approximation within s/c; the clause 0 < w(G) in both promise sets (inherited from the published Max3CutHard.MaxKCutHard) only excludes the edgeless graph, on which both promises hold
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), p.1 ("The result of [CST01] shows that the weighted and unweighted versions of MAX-CUT have the same hardness of approximation (and likewise for MAX-3-CUT)")

import Mathlib
import Definitions.Def_Max3CutHard_MaxKCutHard
import Definitions.Def_HeilmanMax3Cut_MaxKCutHardSimple

namespace HeilmanMax3Cut

/-- **The [CST01] step: weighted and unweighted MAX-3-CUT have the same hardness.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), p.1: "The
result of [CST01] shows that the weighted and unweighted versions of MAX-CUT have the same hardness
of approximation (and likewise for MAX-3-CUT)." [CST01] is P. Crescenzi, R. Silvestri and
L. Trevisan, *On weighted vs unweighted versions of combinatorial optimization problems*,
Inform. Comput. 167 (2001).

For every ratio `r`: MAX-3-CUT on (ℕ-weighted) graphs is NP-hard to approximate within `r + ε` for
every `ε > 0` if and only if MAX-3-CUT on simple graphs is.

**Formalization Note.** "NP-hard to approximate within `r + ε` for every `ε > 0`" is
`∀ ε > 0, ∃ c > 0, s, s/c ≤ r + ε` with `(c, s)`-hardness: the published
`Max3CutHard.MaxKCutHard 3` on ℕ-weighted multigraphs (weights in unary, i.e. polynomially bounded)
and `MaxKCutHardSimple 3` on simple graphs. "The same hardness" is stated as an equivalence. -/
theorem cst01_step (r : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ r + ε ∧ Max3CutHard.MaxKCutHard 3 c s) ↔
      (∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ r + ε ∧ MaxKCutHardSimple 3 c s) := by sorry

end HeilmanMax3Cut
