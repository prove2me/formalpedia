-- Prove2me | Theorems.Thm_MaxEntOCRS_proof_of_theorem_1_add_identity
-- name    : MaxEntOCRS.proof_of_theorem_1_add_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:00.20465+00:00
-- url     : https://prove2.me/theorems/8017ab26-5499-4017-aef1-1cedbc83b0fb
-- title:
--   Proof of Theorem 1 — $\Pr[\mathrm{Add}(e)] = (1 + t_e)\Pr(u, v \text{ both uncovered})$
-- statement:
--   Let $\mu$ be the monomer–dimer measure of a finite loopless multigraph $G$ with activities $t \ge 0$, and let $e = uv$ be an edge (possibly one of several parallel edges). Then
--   $$
--   \Pr_\mu(e \in M) = t_e \Pr_\mu(u, v \text{ both uncovered}), \qquad \Pr_\mu[\mathrm{Add}(e)] = (1 + t_e) \Pr_\mu(u, v \text{ both uncovered}),
--   $$
--   and, if every vertex is covered with probability at most $\alpha$, then $\Pr_\mu[\mathrm{Add}(e)] \ge \alpha$.
--
--   The event $\mathrm{Add}(e)$ is the disjoint union of $\{u, v \text{ both uncovered}\}$ and $\{e \in M\}$. A parallel copy of $e$ in the matching blocks $e$.
--
--   Differences from the source:
--   - generalization: the monomer–dimer measure µ* of Theorem 1's proof (activities positive on the support of x, 0 on deleted edges, occupancies ≤ α) → every monomer–dimer measure with t ≥ 0; the bound ≥ α under the hypothesis that every vertex is covered with probability ≤ α; reason: the identities hold for every nonnegative activity vector and µ* is one; its occupancies are ≤ α by the reduction
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), proof of Theorem 1 from Theorem 2, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_edgeMarginal
import Definitions.Def_MaxEntOCRS_addProb
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_coverProb
import Definitions.Def_MaxEntOCRS_bothUncoveredProb

namespace MaxEntOCRS

/-- Proof of Theorem 1, the addability identity (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.5): for an edge `e = uv` (possibly one
of several parallel edges) and the monomer–dimer measure with nonnegative activities `t`,
`Pr(e ∈ M) = t_e Pr(u, v both uncovered)` and
`Pr[Add(e)] = (1 + t_e) Pr(u, v both uncovered)`, which is `≥ α` (by Theorem 2) when every vertex
is covered with probability at most `α`. Zero activities (the deleted edges) are allowed. -/
theorem proof_of_theorem_1_add_identity {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e)
    (e : E) (u v : V) (he : G.ends e = s(u, v)) :
    edgeMarginal (monomerDimer G t) e = t e * bothUncoveredProb G (monomerDimer G t) u v ∧
      addProb G (monomerDimer G t) e =
        (1 + t e) * bothUncoveredProb G (monomerDimer G t) u v ∧
      ((∀ z : V, coverProb G (monomerDimer G t) z ≤ alpha) →
        alpha ≤ addProb G (monomerDimer G t) e) := by sorry

end MaxEntOCRS
