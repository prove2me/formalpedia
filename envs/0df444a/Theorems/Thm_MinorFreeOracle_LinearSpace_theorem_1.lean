-- Prove2me | Theorems.Thm_MinorFreeOracle_LinearSpace_theorem_1
-- name    : MinorFreeOracle.LinearSpace.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:40.485248+00:00
-- url     : https://prove2.me/theorems/0ae8190a-8456-47ed-9a6a-975f8550f6a6
-- title:
--   Theorem 1 — linear-space exact distance oracle for every excluded minor
-- statement:
--   There is a natural-number constant c such that the following holds for every finite simple graph H and every real ε>0. There exist finite preprocessing and query programs Pre,Qry and a positive constant C, depending only on H and ε, which work for every connected simple n-vertex H-minor-free graph G with nonnegative real edge weights. Preprocessing takes at most Cn^c steps and stores at most Cn cells, counting the input. Every query pair s,t is answered exactly within Cn^(1/2+ε) steps:
--
--   $$
--   T_{\mathrm{pre}}\le Cn^c,\qquad S\le Cn,\qquad
--   T_{\mathrm{query}}(s,t)\le Cn^{1/2+\varepsilon},\qquad
--   \mathrm{answer}(s,t)=d_G(s,t).
--   $$
--
--   The programs are deterministic and fixed before the input graph and its size. The preprocessing exponent is fixed even before H and ε. The statement does not impose strict positivity of weights, a planar special case, or uniqueness of shortest paths. It is the headline oracle theorem, rather than the independent space–query trade-off of Theorem 2.
--
--   Differences from the source:
--   - encoding: a finite undirected simple graph G=(V,E) with nonnegative edge weights → a weighted edge list on Fin n, with IsSimple, nonnegative weights, Connected and the published branch-set Minor relation; reason: finite vertex and edge enumerations preserve every source instance; Connected includes n>0 as in the standing convention
--   - reading: time and space on an unnamed machine model → deterministic finite programs on the published comparison–addition word RAM, with integer word bound (n+m+2)^wordExp; reason: this is the computational model fixed in the planning brief; real values may only be added, negated and compared
--   - encoding: a stored exact distance oracle using O(n) space → halted preprocessing memory; each query starts from it with reset registers; space counts distinct preprocessing writes plus 3+3m input cells; reason: the chosen layout supplies no free input memory or fresh randomness; counting input preserves linear space for simple graphs with a fixed excluded minor
--   - encoding: O(n^c), O(n), O(n^(1/2+ε)), with c independent of H and ε → one natural c before H and ε and one positive real C afterwards bounding all three resources for every n≥1; reason: a larger integer exponent and a common positive constant absorb the source bounds and the finitely many small connected inputs without changing their asymptotic strength
-- source:
--   Eunjin Oh, Linear-Space Exact Distance Oracle for Minor-Free Graphs, STOC 2027 submission #160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/160.pdf, Theorem 1, PDF p.4 (printed p.2); O-constant convention on the same page; preprocessing discussion PDF p.5; standing assumptions §3, PDF p.15

import Mathlib
import Definitions.Def_MinorFreeOracle_LinearSpace_Graph
import Definitions.Def_MinorFreeOracle_LinearSpace_ExactOracle

namespace MinorFreeOracle.LinearSpace

/-- Oh, Theorem 1, PDF p.4 (printed p.2), with the standing connectedness assumption of §3,
PDF p.15. A universal preprocessing exponent, before the excluded minor and epsilon.
The pair of programs and their common positive bound constant are uniform over all input sizes,
all valid enumerations of the graph, and all nonnegative real edge weights. -/
theorem theorem_1 :
    ∃ c : ℕ, ∀ (h : ℕ) (H : SimpleGraph (Fin h)) (ε : ℝ), 0 < ε →
      ∃ (Pre Qry : RealAPSP.Program) (C : ℝ), 0 < C ∧
        ∀ G : TZLevelsADO.Graph,
          IsSimple G → G.Connected → (∀ e, 0 ≤ G.wt e) → MinorFree G H →
          IsExactOracle Pre Qry G
            (C * (G.n : ℝ) ^ c) (C * G.n)
            (C * (G.n : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by sorry

end MinorFreeOracle.LinearSpace
