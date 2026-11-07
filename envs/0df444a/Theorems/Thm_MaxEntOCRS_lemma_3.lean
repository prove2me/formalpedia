-- Prove2me | Theorems.Thm_MaxEntOCRS_lemma_3
-- name    : MaxEntOCRS.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:42.342073+00:00
-- url     : https://prove2.me/theorems/1b6f2c5c-61dd-4d2d-a978-d2c40164c25d
-- title:
--   Lemma 3 — $Z(G) = Z(G')K$ and the vacancy probabilities $1/K$, $Q/K$, $P/K$, $H_i/K$
-- statement:
--   Let $G$ be a finite loopless multigraph with activities $t \ge 0$, let $u \ne v$ be vertices, and use the localization quantities of Section 3: $G' = G - u - v$, the neighbours $y_1, \ldots, y_k$, the law $\nu$ of the free neighbourhood, $K = \mathbb E_\nu D_F$, $P = 1 + \sum_i a_i p_i$, $Q = 1 + \sum_i b_i p_i$ and $H_i = \mathbb E_\nu[X_i D_{F\setminus\{i\}}]$. Under the monomer–dimer measure of $G$,
--   $$
--   Z(G) = Z(G') K ,
--   $$
--   $$
--   \Pr(u, v \text{ uncovered}) = \frac1K, \quad \Pr(u \text{ uncovered}) = \frac QK, \quad \Pr(v \text{ uncovered}) = \frac PK, \quad \Pr(y_i \text{ uncovered}) = \frac{H_i}K .
--   $$
--
--   This expresses the joint vacancy of $u$ and $v$ through the single local quantity $K$, so Theorem 2 becomes $K \le C = 1/\alpha$.
--
--   Differences from the source:
--   - encoding: G′ = G − u − v and its monomer–dimer measure → matchings of G covering neither u nor v, with the restricted measure; reason: the same measure as on the induced subgraph; no subgraph type
--   - encoding: neighbours y₁, …, y_k indexed by [k] → the finite subtype of the neighbour set N; reason: an enumeration is not needed; same index set up to relabelling
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Lemma 3, p.5 (proof in A.1, pp.11–12)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_prob
import Definitions.Def_MaxEntOCRS_Covers
import Definitions.Def_MaxEntOCRS_partitionFn
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_bothUncoveredProb
import Definitions.Def_MaxEntOCRS_deletedPartitionFn
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_Kloc
import Definitions.Def_MaxEntOCRS_Ploc
import Definitions.Def_MaxEntOCRS_Qloc
import Definitions.Def_MaxEntOCRS_Hloc

namespace MaxEntOCRS

/-- Lemma 3 (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.5; detailed proof A.1, pp.11–12): `Z(G) = Z(G′)K`, and
`Pr(u, v uncovered) = 1/K`, `Pr(u uncovered) = Q/K`, `Pr(v uncovered) = P/K`,
`Pr(y_i uncovered) = H_i/K` for every neighbour `y_i`, all under the monomer–dimer measure of
`G` with nonnegative activities `t`, for distinct vertices `u, v`. -/
theorem lemma_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (u v : V) (huv : u ≠ v) :
    partitionFn G t = deletedPartitionFn G t u v * Kloc G t u v ∧
      bothUncoveredProb G (monomerDimer G t) u v = 1 / Kloc G t u v ∧
      prob (monomerDimer G t) (fun M => ¬ Covers G M u) = Qloc G t u v / Kloc G t u v ∧
      prob (monomerDimer G t) (fun M => ¬ Covers G M v) = Ploc G t u v / Kloc G t u v ∧
      ∀ i : nbrSet G u v,
        prob (monomerDimer G t) (fun M => ¬ Covers G M i.1) = Hloc G t u v i / Kloc G t u v := by sorry

end MaxEntOCRS
