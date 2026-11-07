-- Prove2me | Theorems.Thm_MaxEntOCRS_eq_3_normalization
-- name    : MaxEntOCRS.eq_3_normalization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:05.086696+00:00
-- url     : https://prove2.me/theorems/42a617d2-19ab-4068-b344-ebd8b2ff9ba8
-- title:
--   Eq. (3) and Normalization — $0 \le a_i, b_i \le c$; if $K > C$ then $P, Q > \sqrt3$, $r < 1/3$, $r > 0$, $t < 1$
-- statement:
--   Let $G$ have activities $t \ge 0$, let $u \ne v$, and assume every vertex is covered with probability at most $\alpha$. Then
--
--   1. (Eq. (3)) for every neighbour index $i$, $0 \le a_i \le c$ and $0 \le b_i \le c$, where $c = 1/\sqrt3$;
--   2. (Normalization) if moreover $K > C$, then with $U = 1/P$, $V = 1/Q$, $x_i = a_i/P$, $y_i = b_i/Q$, $z_i = (x_i + y_i)/2$, $r = \max_i z_i$, $\kappa = K/(PQ)$ and $t = 1 - \kappa$:
--   $$
--   P > \sqrt3,\quad Q > \sqrt3,\quad U < c,\quad V < c,\quad x_j \le cU,\quad y_j \le cV,\quad r < c^2 = \tfrac13,
--   $$
--   the neighbourhood is nonempty ($k \ge 1$), $r > 0$ and $t < 1$.
--
--   These normalizations set up the two scalar inequalities (4) and (5).
--
--   The second part is a step of the paper's proof by contradiction ("Suppose for contradiction that $K > C$"). By Theorem 2 the occupancy hypothesis forces $K \le C$, so the hypotheses occupancy $\le \alpha$ and $K > C$ never hold together; the second part is the intermediate step as printed, not an independent fact about some instance.
--
--   **Formalization Note** The paper's $t = 1-\kappa$ is named $t_N$, because $t$ also denotes the activities.
--
--   Differences from the source:
--   - encoding: U = 1/P, V = 1/Q, x_i = a_i/P, y_i = b_i/Q, z_i = (x_i + y_i)/2, r = max_i z_i, κ = K/(PQ), t = 1 − κ → U, V, x_i, y_i written out; r, κ, t bound by defining equations, r as the supremum over the neighbour subtype, t named tN; reason: names for the paper's values; the supremum over a finite nonempty type is the maximum, and t clashes with the activities
--   - encoding: G′ = G − u − v and its monomer–dimer measure → matchings of G covering neither u nor v, with the restricted measure; reason: the same measure as on the induced subgraph; no subgraph type
--   - encoding: neighbours y₁, …, y_k indexed by [k] → the finite subtype of the neighbour set N; reason: an enumeration is not needed; same index set up to relabelling
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Eq. (3) and the Normalization paragraph, p.7 (A.7, p.14)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_bigC
import Definitions.Def_MaxEntOCRS_smallC
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_coverProb
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_pairWt
import Definitions.Def_MaxEntOCRS_Kloc
import Definitions.Def_MaxEntOCRS_Ploc
import Definitions.Def_MaxEntOCRS_Qloc

namespace MaxEntOCRS

/-- Eq. (3) and the Normalization paragraph of the proof of Theorem 2 (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.7; A.7, p.14).
Under the hypothesis of Theorem 2, `0 ≤ a_i, b_i ≤ c = 1/√3` for every neighbour (Eq. (3)). If
moreover `K > C`, then with `U = 1/P`, `V = 1/Q`, `x_i = a_i/P`, `y_i = b_i/Q`,
`z_i = (x_i + y_i)/2`, `r = max_i z_i`, `κ = K/(PQ)` and `t = 1 − κ`: `P, Q > √3`, `U, V < c`,
`x_j ≤ cU`, `y_j ≤ cV`, `r < c² = 1/3`, `k ≥ 1`, `r > 0` and `t < 1`.

**Formalization Note** The paper's `t = 1 − κ` is named `tN` (the paper also uses `t` for the
activities); `U, V, x_i, y_i` are written out; `r` is `⨆` over the neighbour subtype, which is
the maximum when `k ≥ 1`.

This is a step of the paper's proof by contradiction: by Theorem 2 the occupancy hypothesis
forces `K ≤ C`, so the hypotheses never hold together. -/
theorem eq_3_normalization {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (u v : V) (huv : u ≠ v)
    (hocc : ∀ z : V, coverProb G (monomerDimer G t) z ≤ alpha) (kappa tN r : ℝ)
    (hkappa : kappa = Kloc G t u v / (Ploc G t u v * Qloc G t u v)) (htN : tN = 1 - kappa)
    (hr : r = ⨆ i : nbrSet G u v,
      (pairWt G t u i.1 / Ploc G t u v + pairWt G t v i.1 / Qloc G t u v) / 2) :
    (∀ i : nbrSet G u v, 0 ≤ pairWt G t u i.1 ∧ pairWt G t u i.1 ≤ smallC) ∧
      (∀ i : nbrSet G u v, 0 ≤ pairWt G t v i.1 ∧ pairWt G t v i.1 ≤ smallC) ∧
      (bigC < Kloc G t u v →
        Real.sqrt 3 < Ploc G t u v ∧ Real.sqrt 3 < Qloc G t u v ∧
          1 / Ploc G t u v < smallC ∧ 1 / Qloc G t u v < smallC ∧
          (∀ j : nbrSet G u v, pairWt G t u j.1 / Ploc G t u v ≤ smallC * (1 / Ploc G t u v)) ∧
          (∀ j : nbrSet G u v, pairWt G t v j.1 / Qloc G t u v ≤ smallC * (1 / Qloc G t u v)) ∧
          r < 1 / 3 ∧ Nonempty (nbrSet G u v) ∧ 0 < r ∧ tN < 1) := by sorry

end MaxEntOCRS
