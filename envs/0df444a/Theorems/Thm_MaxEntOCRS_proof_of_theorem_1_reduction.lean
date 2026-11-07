-- Prove2me | Theorems.Thm_MaxEntOCRS_proof_of_theorem_1_reduction
-- name    : MaxEntOCRS.proof_of_theorem_1_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:45.454138+00:00
-- url     : https://prove2.me/theorems/e310fea1-7349-4edf-8080-c8fd626802e1
-- title:
--   Proof of Theorem 1 — the maximum-entropy distribution with marginals $\alpha x$ is monomer–dimer, with occupancies $m_z = \sum_{e\ni z}\alpha x_e \le \alpha$
-- statement:
--   Let $G = (V, E)$ be a finite loopless multigraph and $x$ a point of the fractional matching polytope
--   $$
--   P(G) = \Big\{ x \ge 0 : \sum_{e \ni v} x_e \le 1 \text{ for all } v \Big\}.
--   $$
--   Then:
--
--   1. a maximum-entropy distribution on $\mathcal M(G)$ with marginals $\alpha x$ exists;
--   2. every such distribution $\mu^*$ is the monomer–dimer measure of $G$ with some activities $t \ge 0$ that are positive exactly on the edges with $x_e > 0$ (and $0$ on the deleted edges with $x_e = 0$);
--   3. its covering probabilities are
--   $$
--   m_z = \sum_{e \ni z} \alpha x_e \le \alpha \qquad \text{for every vertex } z .
--   $$
--
--   This reduces Theorem 1 to Theorem 2, a statement about monomer–dimer measures with occupancies at most $\alpha$.
--
--   Differences from the source:
--   - reading: µ* (the maximum-entropy distribution) is a monomer–dimer measure with finite positive activities, activity 0 on the deleted edges → a maximizer exists, and every maximizer equals monomerDimer G t for some t ≥ 0 with t_e = 0 ↔ x_e = 0; reason: the definite article asserts existence; the maximizer is unique, so 'every' and 'the' agree
--   - encoding: distributions on M(G) → weight functions on Finset E, nonnegative, vanishing off matchings, summing to 1; reason: Lean convention; same distributions
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), proof of Theorem 1 from Theorem 2, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_OnlineCRS_Matching_Model
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_IsMaxEntropy
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_coverProb

namespace MaxEntOCRS

/-- Proof of Theorem 1 from Theorem 2, the reduction (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.5): for every finite loopless
multigraph `G` and every `x ∈ P(G)`, a maximum-entropy distribution with marginals `αx` exists,
and every such distribution is the monomer–dimer measure with nonnegative activities that are
positive exactly on the support of `x` ("µ* is a monomer–dimer measure with finite positive
activities [ANN26, Lemma 1]; assign activity 0 to the deleted edges"); its covering
probabilities are `m_z = ∑_{e ∋ z} α x_e ≤ α`. -/
theorem proof_of_theorem_1_reduction {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (hx : x ∈ OnlineCRS.Matching.matchingRelax G) :
    (∃ μ, IsMaxEntropy G (alpha • x) μ) ∧
      ∀ μ, IsMaxEntropy G (alpha • x) μ →
        (∃ t : E → ℝ, (∀ e, 0 ≤ t e) ∧ (∀ e, t e = 0 ↔ x e = 0) ∧ μ = monomerDimer G t) ∧
        ∀ z : V, coverProb G μ z = ∑ e ∈ OnlineCRS.Matching.edgeStar G z, alpha * x e ∧
          coverProb G μ z ≤ alpha := by sorry

end MaxEntOCRS
