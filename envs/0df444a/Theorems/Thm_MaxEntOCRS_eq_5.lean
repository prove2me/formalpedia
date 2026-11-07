-- Prove2me | Theorems.Thm_MaxEntOCRS_eq_5
-- name    : MaxEntOCRS.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:25.204239+00:00
-- url     : https://prove2.me/theorems/cbb246f5-4a62-4b7c-ac54-71b72a1f630e
-- title:
--   Eq. (5) — the cross-term bound $t \le r(\alpha + \beta t)$
-- statement:
--   Let $G$ have activities $t \ge 0$ and $u \ne v$, assume every vertex is covered with probability at most $\alpha$, and suppose $K > C$. With $r = \max_i z_i$, $\kappa = K/(PQ)$ and the normalized cross term $t_N = 1 - \kappa$,
--   $$
--   t_N \le r(\alpha + \beta t_N) .
--   $$
--
--   It combines the expansion (2), Lemma 8 and the constraints $U, V \ge \beta\kappa$.
--
--   These inequalities are steps of the paper's proof by contradiction ("Suppose for contradiction that $K > C$"). By Theorem 2 the occupancy hypothesis forces $K \le C$, so the hypotheses occupancy $\le \alpha$ and $K > C$ never hold together; the statement is the intermediate step as printed, not an independent fact about some instance.
--
--   Differences from the source:
--   - encoding: U = 1/P, V = 1/Q, x_i = a_i/P, y_i = b_i/Q, z_i = (x_i + y_i)/2, r = max_i z_i, κ = K/(PQ), t = 1 − κ → U, V, x_i, y_i written out; r, κ, t bound by defining equations, r as the supremum over the neighbour subtype, t named tN; reason: names for the paper's values; the supremum over a finite nonempty type is the maximum, and t clashes with the activities
--   - encoding: G′ = G − u − v and its monomer–dimer measure → matchings of G covering neither u nor v, with the restricted measure; reason: the same measure as on the induced subgraph; no subgraph type
--   - encoding: neighbours y₁, …, y_k indexed by [k] → the finite subtype of the neighbour set N; reason: an enumeration is not needed; same index set up to relabelling
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Eq. (5), p.8 (A.7, p.15)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_beta
import Definitions.Def_MaxEntOCRS_bigC
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_coverProb
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_pairWt
import Definitions.Def_MaxEntOCRS_Kloc
import Definitions.Def_MaxEntOCRS_Ploc
import Definitions.Def_MaxEntOCRS_Qloc

namespace MaxEntOCRS

/-- Eq. (5), the bound on the normalized cross term (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.8; A.7, p.15). Under the
hypothesis of Theorem 2 and `K > C`, with `r = max_i z_i`, `κ = K/(PQ)` and `t = 1 − κ` as in
the Normalization paragraph: `t ≤ r(α + βt)`.

**Formalization Note** `tN` is the paper's `t = 1 − κ`; `r` is `⨆` over the neighbour subtype.

This is a step of the paper's proof by contradiction: by Theorem 2 the occupancy hypothesis
forces `K ≤ C`, so the hypotheses never hold together. -/
theorem eq_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (u v : V) (huv : u ≠ v)
    (hocc : ∀ z : V, coverProb G (monomerDimer G t) z ≤ alpha) (kappa tN r : ℝ)
    (hkappa : kappa = Kloc G t u v / (Ploc G t u v * Qloc G t u v)) (htN : tN = 1 - kappa)
    (hr : r = ⨆ i : nbrSet G u v,
      (pairWt G t u i.1 / Ploc G t u v + pairWt G t v i.1 / Qloc G t u v) / 2)
    (hK : bigC < Kloc G t u v) :
    tN ≤ r * (alpha + beta * tN) := by sorry

end MaxEntOCRS
