-- Prove2me | Theorems.Thm_HeilmanMax3Cut_theorem_1_4
-- name    : HeilmanMax3Cut.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:20.264793+00:00
-- url     : https://prove2.me/theorems/33e5eff0-bf00-4ce7-b728-a6db86552cee
-- title:
--   Theorem 1.4 — sharp UG-hardness of MAX-3-CUT
-- statement:
--   Assume the Unique Games Conjecture. Then for every $\varepsilon>0$ it is NP-hard to approximate MAX-3-CUT within $\alpha_3+\varepsilon$: there are $c>0$ and $s$ with
--
--   $$\frac sc\ \le\ \alpha_3+\varepsilon$$
--
--   such that it is NP-hard to distinguish simple graphs $G$ with $\max_\chi\mathrm{cut}_\chi(G)\ge c\,|E(G)|$ from simple graphs with $\max_\chi\mathrm{cut}_\chi(G)\le s\,|E(G)|$, where $\chi$ ranges over 3-colourings of the vertices. Here $\alpha_3\approx.83600811464$ is the Frieze–Jerrum ratio (2).
--
--   Since the Frieze–Jerrum algorithm achieves $\alpha_3$ in polynomial time, the theorem determines the approximability threshold of MAX-3-CUT under the Unique Games Conjecture.
--
--   Differences from the source:
--   - reading: the Unique Games Conjecture [Kho02, KN10] (paraphrased on p.5 in the linear-equations form) → the published OptInapprox.MaxCut.UGC (Khot's Unique Label Cover form); reason: Theorem 1.4 cites [Kho02, KN10], where the conjecture is stated for Unique Label Cover
--   - encoding: NP-hard to approximate MAX-3-CUT within α₃ + ε → ∃ c > 0, s with s/c ≤ α₃ + ε and (c, s)-gap NP-hardness, both promise sets restricted to graphs with at least one edge (MaxKCutHardSimple 3, simple graphs); reason: (c, s)-hardness is the form the reductions produce, and it implies NP-hardness of approximation within s/c; the clause 0 < w(G) in both promise sets (inherited from the published Max3CutHard.MaxKCutHard) only excludes the edgeless graph, on which both promises hold
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.4, p.4

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_HeilmanMax3Cut_alpha3
import Definitions.Def_HeilmanMax3Cut_MaxKCutHardSimple
open OptInapprox.MaxCut

namespace HeilmanMax3Cut

/-- **Theorem 1.4 (Sharp Hardness for MAX-3-CUT).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.4, p.4: "Assume the Unique
Games Conjecture holds. Then, for any `ε > 0`, it is NP-hard to approximate MAX-3-CUT within
`α₃ + ε`." MAX-3-CUT (§1.1, p.3) asks for the partition of the vertices of a finite undirected
graph into three sets maximizing the number of edges between the sets; `α₃ ≈ .83600811464` is the
Frieze–Jerrum ratio (2).

**Formalization Note.** The UGC is the published `OptInapprox.MaxCut.UGC` (Khot's Unique Label
Cover form, [Kho02, KN10]). "NP-hard to approximate within `α₃ + ε`" is: there are `c > 0` and `s`
with `s/c ≤ α₃ + ε` such that it is NP-hard to distinguish simple graphs with
`max_χ cut_χ(G) ≥ c|E|` from simple graphs with `max_χ cut_χ(G) ≤ s|E|` (`MaxKCutHardSimple 3`).
Graphs are simple (unweighted), as in the paper's problem statement. -/
theorem theorem_1_4 (hUGC : UGC) :
    ∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ alpha3 + ε ∧ MaxKCutHardSimple 3 c s := by sorry

end HeilmanMax3Cut
