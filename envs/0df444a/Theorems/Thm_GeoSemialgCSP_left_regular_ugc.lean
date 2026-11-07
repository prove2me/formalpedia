-- Prove2me | Theorems.Thm_GeoSemialgCSP_left_regular_ugc
-- name    : GeoSemialgCSP.left_regular_ugc
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:39.89555+00:00
-- url     : https://prove2.me/theorems/5c01e2f2-91d9-4039-9264-ec6c9de36239
-- title:
--   §6, p.17 — left-regular Unique Games hardness [KKMO 2007, §8.1]
-- statement:
--   This is the left-regular bipartite formulation of the Unique Games Conjecture of Khot, Kindler, Mossel and O'Donnell (2007, Section 3, Definition 1 and the conjecture following it), with their remark (Section 8.1) that the bipartite graph may be assumed regular on the left side.
--
--   Assume the Unique Games Conjecture. Then for every $\varepsilon_{UG},s_{UG}>0$ there is a constant alphabet size $M$ such that it is NP-hard to distinguish Unique Games instances over alphabet $[M]$ that are regular on the left side and have value at least $1-\varepsilon_{UG}$ from such instances of value at most $s_{UG}$. Instances may have parallel edges, each with its own permutation, and have at least one edge.
--
--   The reduction of Section 6 starts from these instances; left regularity makes "a uniform left vertex, then a uniform incident edge" a uniform edge.
--
--   Differences from the source:
--   - encoding: the Unique Games Conjecture of Khot (KKMO07, §3) → the published OptInapprox.MaxCut.UGC; reason: the same conjecture: for all η, γ > 0 some alphabet size makes the 1 − η vs γ gap NP-hard
--   - encoding: a bipartite constraint graph regular on U, parallel edges allowed → MULC: a list of edge occurrences with permutations; LeftRegular: equal numbers of occurrences at every left vertex; reason: same instances
--   - encoding: for a sufficiently large constant alphabet size R → ∃ M : ℕ with alphabet Fin M; reason: as in the published UGC
--   - encoding: instances (implicitly with edges) → edges ≠ [] in both promise sets; reason: excludes only edgeless instances, whose value 0 is not meaningful; as in the published UGC (E.Nonempty)
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, p.17 (PDF p.18), citing Khot–Kindler–Mossel–O'Donnell 2007, §3 Definition 1 and §8.1

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_GeoSemialgCSP_MULC
import Definitions.Def_GeoSemialgCSP_MULC_OPT
import Definitions.Def_GeoSemialgCSP_MULC_LeftRegular
import Definitions.Def_GeoSemialgCSP_encMULC

namespace GeoSemialgCSP

/-- **The left-regular Unique Games Conjecture.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, printed p.17 (PDF p.18), citing Khot,
Kindler, Mossel, O'Donnell (2007, §3 Definition 1 and §8.1): under the Unique Games Conjecture the
bipartite graph may be assumed regular on the left side; for every `ε_UG, s_UG > 0`, for a
sufficiently large constant alphabet size it is NP-hard to distinguish left-regular instances of
value at least `1 − ε_UG` from instances of value at most `s_UG`.

**Formalization Note.** The hypothesis is the published Unique Games Conjecture
`OptInapprox.MaxCut.UGC` (Khot's bipartite form). Instances may have parallel edges, as the page
allows ("parallel edges, if present, are distinguished as edge occurrences"); both promise sets
require at least one edge and left regularity. -/
theorem left_regular_ugc (hUGC : OptInapprox.MaxCut.UGC) :
    ∀ η γ : ℝ, 0 < η → 0 < γ → ∃ M : ℕ,
      OptInapprox.MaxCut.GapNPHard encMULC
        (fun L : MULC => L.M = M ∧ L.edges ≠ [] ∧ L.LeftRegular ∧ 1 - η ≤ L.OPT)
        (fun L : MULC => L.M = M ∧ L.edges ≠ [] ∧ L.LeftRegular ∧ L.OPT ≤ γ) := by sorry

end GeoSemialgCSP
