-- Prove2me | Theorems.Thm_MaxEntOCRS_section_6_continuity
-- name    : MaxEntOCRS.section_6_continuity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:04.391768+00:00
-- url     : https://prove2.me/theorems/8ae38ef5-5fa2-4d7e-bf34-7293c9be9ed1
-- title:
--   Section 6, Tightness — the maximum-entropy distribution exists, is unique and depends continuously on the marginals
-- statement:
--   Let $G$ be a finite loopless multigraph. Then:
--
--   1. for every marginal vector $q$ of the matching polytope (that is, $q$ is the marginal vector of some distribution on $\mathcal M(G)$), there is exactly one maximum-entropy distribution on $\mathcal M(G)$ with marginals $q$;
--   2. this distribution depends continuously on the marginals on the whole matching polytope, including its boundary: if $q_n \to q$, $\mu_n$ is the maximum-entropy distribution with marginals $q_n$ and $\mu$ the one with marginals $q$, then $\mu_n \to \mu$.
--
--   The tightness argument for Theorem 1 uses this to pass to the limit $\delta \to 0$ on the four-cycle with a diagonal.
--
--   **Formalization Note** The matching polytope is the set of achievable marginal vectors (the convex hull of the matching indicators). Continuity is stated sequentially, which is equivalent in finite dimension.
--
--   Differences from the source:
--   - encoding: the matching polytope → the set of marginal vectors of distributions on M(G); reason: equal to the convex hull of the matching indicator vectors; no Edmonds description needed
--   - reading: continuity of entropy and uniqueness of its maximizer imply that the maximum-entropy distribution depends continuously on the marginals → existence and uniqueness of the maximizer at every point of the polytope, and sequential continuity of the maximizer; reason: the sentence asserts uniqueness and that the maximizer is a function of the marginals; sequential continuity is continuity in finite dimension
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 6, Tightness, p.8

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_IsMatchingDist
import Definitions.Def_MaxEntOCRS_edgeMarginal
import Definitions.Def_MaxEntOCRS_IsMaxEntropy

namespace MaxEntOCRS

/-- Section 6, Tightness, the continuity of the entropy maximizer (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.8): for a finite
configuration set, the maximum-entropy distribution with prescribed marginals exists and is
unique for every marginal vector of the matching polytope, and it depends continuously on the
marginals on the whole matching polytope, including its boundary.

**Formalization Note** The matching polytope is the set of marginal vectors `q` achieved by
some distribution on matchings (the convex hull of the matching indicators). Continuity is
sequential (equivalent here: all spaces are finite-dimensional), in the product topology on
weight functions. -/
theorem section_6_continuity {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) :
    (∀ q : E → ℝ, (∃ μ, IsMatchingDist G μ ∧ ∀ e, edgeMarginal μ e = q e) →
        ∃! μ, IsMaxEntropy G q μ) ∧
      ∀ (qs : ℕ → E → ℝ) (q : E → ℝ) (μs : ℕ → Finset E → ℝ) (μ : Finset E → ℝ),
        Filter.Tendsto qs Filter.atTop (nhds q) → (∀ n, IsMaxEntropy G (qs n) (μs n)) →
          IsMaxEntropy G q μ → Filter.Tendsto μs Filter.atTop (nhds μ) := by sorry

end MaxEntOCRS
