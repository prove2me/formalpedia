-- Prove2me | Theorems.Thm_MaxEntOCRS_eq_4
-- name    : MaxEntOCRS.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:37.351024+00:00
-- url     : https://prove2.me/theorems/577dadb8-88e3-4659-8770-b025eb4ec759
-- title:
--   Eq. (4) — the constraint at the heaviest neighbour, $2r(1-r) \le \alpha\kappa$
-- statement:
--   Let $G$ have activities $t \ge 0$ and $u \ne v$, assume every vertex is covered with probability at most $\alpha$, and suppose $K > C$. With $r = \max_i z_i$ and $\kappa = K/(PQ)$ as in the Normalization paragraph,
--   $$
--   2r(1 - r) \le \alpha \kappa .
--   $$
--
--   It comes from the occupancy constraint $M_i = K - H_i \le \alpha K$ at a neighbour $i$ with $z_i = r$, together with Lemma 6.
--
--   These inequalities are steps of the paper's proof by contradiction ("Suppose for contradiction that $K > C$"). By Theorem 2 the occupancy hypothesis forces $K \le C$, so the hypotheses occupancy $\le \alpha$ and $K > C$ never hold together; the statement is the intermediate step as printed, not an independent fact about some instance.
--
--   Differences from the source:
--   - encoding: U = 1/P, V = 1/Q, x_i = a_i/P, y_i = b_i/Q, z_i = (x_i + y_i)/2, r = max_i z_i, κ = K/(PQ), t = 1 − κ → U, V, x_i, y_i written out; r, κ, t bound by defining equations, r as the supremum over the neighbour subtype, t named tN; reason: names for the paper's values; the supremum over a finite nonempty type is the maximum, and t clashes with the activities
--   - encoding: G′ = G − u − v and its monomer–dimer measure → matchings of G covering neither u nor v, with the restricted measure; reason: the same measure as on the induced subgraph; no subgraph type
--   - encoding: neighbours y₁, …, y_k indexed by [k] → the finite subtype of the neighbour set N; reason: an enumeration is not needed; same index set up to relabelling
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Eq. (4), p.8 (A.7, pp.14–15)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_bigC
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_coverProb
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_pairWt
import Definitions.Def_MaxEntOCRS_Kloc
import Definitions.Def_MaxEntOCRS_Ploc
import Definitions.Def_MaxEntOCRS_Qloc

namespace MaxEntOCRS

/-- Eq. (4), the constraint at the heaviest neighbour (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.8; A.7, pp.14–15). Under the
hypothesis of Theorem 2 and `K > C`, with `r = max_i z_i` and `κ = K/(PQ)` as in the
Normalization paragraph: `2r(1 − r) ≤ ακ`.

**Formalization Note** As in `eq_3_normalization`, `r` is `⨆` over the neighbour subtype.

This is a step of the paper's proof by contradiction: by Theorem 2 the occupancy hypothesis
forces `K ≤ C`, so the hypotheses never hold together. -/
theorem eq_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (u v : V) (huv : u ≠ v)
    (hocc : ∀ z : V, coverProb G (monomerDimer G t) z ≤ alpha) (kappa r : ℝ)
    (hkappa : kappa = Kloc G t u v / (Ploc G t u v * Qloc G t u v))
    (hr : r = ⨆ i : nbrSet G u v,
      (pairWt G t u i.1 / Ploc G t u v + pairWt G t v i.1 / Qloc G t u v) / 2)
    (hK : bigC < Kloc G t u v) :
    2 * r * (1 - r) ≤ alpha * kappa := by sorry

end MaxEntOCRS
