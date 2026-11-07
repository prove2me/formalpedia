-- Prove2me | Theorems.Thm_MaxEntOCRS_eq_1_2
-- name    : MaxEntOCRS.eq_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:06.942968+00:00
-- url     : https://prove2.me/theorems/41361d16-67e2-48fa-b20d-cdcc2122a4bf
-- title:
--   Eqs. (1)–(2) — $Q, P, H_i \ge \beta K$ under the occupancy hypothesis, and $K = PQ - a^{\mathsf T}\Delta b + w$
-- statement:
--   In the setting of Lemma 3 (activities $t \ge 0$, distinct vertices $u, v$):
--
--   1. (Eq. (1)) if every vertex is covered with probability at most $\alpha$, then
--   $$
--   Q \ge \beta K, \qquad P \ge \beta K, \qquad H_i \ge \beta K \quad (i \in [k]) ;
--   $$
--   2. (Eq. (2)) expanding the expectation,
--   $$
--   K = PQ - a^{\mathsf T} \Delta b + w, \qquad \Delta_{ii} = p_i^2, \quad \Delta_{ij} = p_i p_j - p_{ij} \ (i \ne j),
--   $$
--   where $a_i, b_i$ are the aggregated activities between $u$, resp. $v$, and $y_i$, and $w$ is the aggregated activity between $u$ and $v$.
--
--   These are the linear constraints and the expansion on which the proof of Theorem 2 operates.
--
--   Differences from the source:
--   - encoding: G′ = G − u − v and its monomer–dimer measure → matchings of G covering neither u nor v, with the restricted measure; reason: the same measure as on the induced subgraph; no subgraph type
--   - encoding: neighbours y₁, …, y_k indexed by [k] → the finite subtype of the neighbour set N; reason: an enumeration is not needed; same index set up to relabelling
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Eqs. (1) and (2), p.5 (A.1, p.12)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_beta
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_coverProb
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_pairWt
import Definitions.Def_MaxEntOCRS_freeLaw
import Definitions.Def_MaxEntOCRS_DeltaMat
import Definitions.Def_MaxEntOCRS_Kloc
import Definitions.Def_MaxEntOCRS_Ploc
import Definitions.Def_MaxEntOCRS_Qloc
import Definitions.Def_MaxEntOCRS_Hloc

namespace MaxEntOCRS

/-- Eqs. (1) and (2) (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.5; A.1, p.12). Under the hypothesis of Theorem 2 (every vertex is
covered with probability at most `α`), `Q ≥ βK`, `P ≥ βK` and `H_i ≥ βK` for every `i ∈ [k]`
(Eq. (1)); and, expanding the expectation, `K = PQ − aᵀΔb + w` (Eq. (2)). -/
theorem eq_1_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (u v : V) (huv : u ≠ v) :
    ((∀ z : V, coverProb G (monomerDimer G t) z ≤ alpha) →
        beta * Kloc G t u v ≤ Qloc G t u v ∧ beta * Kloc G t u v ≤ Ploc G t u v ∧
          ∀ i : nbrSet G u v, beta * Kloc G t u v ≤ Hloc G t u v i) ∧
      Kloc G t u v = Ploc G t u v * Qloc G t u v -
          ∑ i : nbrSet G u v, ∑ j : nbrSet G u v,
            pairWt G t u i.1 * DeltaMat (freeLaw G t u v) i j * pairWt G t v j.1 +
        pairWt G t u v := by sorry

end MaxEntOCRS
