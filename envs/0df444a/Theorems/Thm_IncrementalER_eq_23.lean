-- Prove2me | Theorems.Thm_IncrementalER_eq_23
-- name    : IncrementalER.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:19.271188+00:00
-- url     : https://prove2.me/theorems/8861373d-9177-4f92-b5e7-a3d95c836043
-- title:
--   (23), p.38 — a star of conductance $\varepsilon c^*/(16Un^3)$ changes feasible energies by at most a factor $1-\varepsilon/16$
-- statement:
--   Let $\hat G$ be a multigraph on $n$ vertices with positive capacities, and let $c^*>0$ and $U$ be such that every capacity $c_e$ of $\hat G$ satisfies $c^*\le Uc_e$. Let $r$ be an endpoint of an edge of $\hat G$, let $W$ be the set of vertices incident to an edge of $\hat G$, and let $G=\hat G+S$, where $S$ is the star joining $r$ to every other vertex of $W$ with conductance
--
--   $$\delta=\frac{\varepsilon c^*}{16Un^3},\qquad\varepsilon>0 .$$
--
--   Then every componentwise feasible demand $d$ (zero sum on every connected component of $\hat G$) satisfies
--
--   $$\Big(1-\frac{\varepsilon}{16}\Big)d^\top L_{\hat G}^\dagger d\le d^\top L_G^\dagger d\le d^\top L_{\hat G}^\dagger d.\tag{23}$$
--
--   This makes the input graph connected at a negligible cost in accuracy.
--
--   Differences from the source:
--   - generalization: c∗ the first inserted conductance and U the capacity ratio of the input graph → any c∗ > 0 and U with c∗ ≤ U·c_e for every edge e; reason: the paper's c∗ and U satisfy this, and it is the only consequence the proof uses
--   - generalization: 0 < ε < 1/2 → 0 < ε; reason: the bound holds for every ε > 0 by the same argument; it specializes to the paper's range
--   - encoding: Ĝ the input graph restricted to the vertices incident to inserted edges → Ĝ an edge list on all n vertices, the others isolated; feasibility forces d = 0 on them; reason: the paper notes that a feasible demand has 0 demand on every omitted vertex (p.38)
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), proof of Theorem 1.1, connectivity augmentation and (23), p.38

import Mathlib
import Definitions.Def_IncrementalER_Edge
import Definitions.Def_IncrementalER_energy

namespace IncrementalER

/-- **(23)** (connectivity augmentation by a light star), proof of Theorem 1.1.

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), proof of Theorem 1.1,
"Connectivity augmentation" and (23), p.38.

Let `Ĝ` be a multigraph on `n` vertices with positive capacities, `c∗ > 0` and `U` such that every
capacity is at least `c∗ / U`, `r` an endpoint of an edge of `Ĝ`, and `G = Ĝ + S` where `S` is the
star from `r` to every other vertex incident to an edge of `Ĝ`, each star edge of conductance
`δ = ε c∗ / (16 U n³)`. Then every componentwise feasible demand `d` satisfies
`(1 − ε/16) d⊤L†_Ĝ d ≤ d⊤L†_G d ≤ d⊤L†_Ĝ d`.

**Formalization Note.**
* The paper takes `c∗` the first inserted conductance and `U` the capacity ratio of the input
  graph, so `c∗ ≤ U c_e` for every edge; only this consequence is assumed (a generalization).
* `ε > 0` is arbitrary (the paper has `0 < ε < 1/2`; a generalization).
* `Ĝ` and `G` are edge lists on `Fin n`; vertices of `Fin n` with no incident edge are isolated in
  both, and componentwise feasibility (zero sum on every component of `Ĝ`, isolated vertices
  included) forces `d` to vanish on them, as on p.38 ("A feasible demand vector must have `0`
  demand on every omitted vertex"). -/
theorem eq_23 {n : ℕ} (es : List (Edge n)) (hpos : ∀ e ∈ es, 0 < e.c) (cstar U ε : ℝ)
    (hcstar : 0 < cstar) (hU : ∀ e ∈ es, cstar ≤ U * e.c) (hε : 0 < ε) (r : Fin n)
    (hr : ∃ e ∈ es, e.u = r ∨ e.v = r) (d : Fin n → ℝ) (hd : ComponentFeasible es d) :
    let W : Finset (Fin n) := Finset.univ.filter fun x => ∃ e ∈ es, e.u = x ∨ e.v = x
    let δ : ℝ := ε * cstar / (16 * U * (n : ℝ) ^ 3)
    let star : List (Edge n) := (W.erase r).toList.map fun w => ⟨r, w, δ⟩
    (1 - ε / 16) * energy (edgeLap es) d ≤ energy (edgeLap (es ++ star)) d ∧
      energy (edgeLap (es ++ star)) d ≤ energy (edgeLap es) d := by sorry

end IncrementalER
