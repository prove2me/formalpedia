-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_lemma_2_6
-- name    : KleeWalkup67.FiveStep.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T05:49:18.992551+00:00
-- url     : https://prove2.me/theorems/a203c800-2e39-4d64-80ac-eadcc06ae569
-- title:
--   Lemma 2.6 — simplification with a surjection of face complexes
-- statement:
--   Let $P$ be any nonsimple polyhedron of class $(d,n)$. There is a simple polyhedron $Q$ of that same class, bounded if and only if $P$ is bounded, and a map $\theta:\mathcal K(Q)\to\mathcal K(P)$ such that
--   $$G\subseteq F\ \Longrightarrow\ \theta(G)\subseteq\theta(F),\qquad
--   \dim\theta(F)\le\dim F.$$
--   Every face $H$ of $P$ has a preimage $F$ with $\dim F=\dim H$. In particular, the map is onto. Both complexes contain the improper face and exclude the empty set. The lemma supplies the geometric reduction from nonsimple polyhedra while preserving boundedness.
--
--   Differences from the source:
--   - encoding: d-dimensional polyhedra in finite-dimensional real vector spaces with n geometric facets → irredundant real facet presentations in EuclideanSpace ℝ (Fin d) with n rows; reason: choose affine coordinates in the affine hull; nonempty interior and irredundancy preserve exactly the source instances
--   - encoding: pointed simple polyhedra have exactly d edges at each vertex → the published IsSimple counts exactly d incident facets at each vertex; reason: these characterizations are equivalent for pointed d-polyhedra with geometric facet presentations
--   - encoding: a mapping onto the nonempty face complex with a same-dimensional preimage of every face → a function between face subtypes with an explicit same-dimensional preimage for each target face; reason: face subtypes contain the actual geometric sets; the final quantified clause already implies surjectivity
-- source:
--   Klee and Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Mathematica 117 (1967), 53–78, https://doi.org/10.1007/BF02395040, p.60 (PDF8), Lemma 2.6.

import Definitions.Def_KleeWalkup67_Support_Classes

namespace KleeWalkup67.FiveStep

theorem lemma_2_6 {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hP : Support.IsClass a b) (hNS : ¬ IsSimple a b) :
    ∃ (a' : Fin n → EuclideanSpace ℝ (Fin d)) (b' : Fin n → ℝ),
      Support.IsClass a' b' ∧ IsSimple a' b' ∧
      (Bornology.IsBounded (Hirsch.Hpoly a' b') ↔
        Bornology.IsBounded (Hirsch.Hpoly a b)) ∧
      ∃ θ : Support.FaceComplex a' b' → Support.FaceComplex a b,
        (∀ F G, G.val ⊆ F.val → (θ G).val ⊆ (θ F).val) ∧
        (∀ F, dim (θ F).val ≤ dim F.val) ∧
        (∀ H, ∃ F, θ F = H ∧ dim F.val = dim H.val) := by sorry

end KleeWalkup67.FiveStep
