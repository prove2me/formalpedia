-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_14
-- name    : Gomory69.Asymptotic.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:26:43.446347+00:00
-- url     : https://prove2.me/theorems/6f1b8362-00a0-495e-984f-db1c56ae4cea
-- title:
--   THEOREM 14 — Automorphisms transport facets and their constants
-- statement:
--   Let $G$ be a finite Abelian group, let $(\pi,\pi_0)$ be a facet of $P(G,g_0)$ and let $\varphi:G\to G$ be any additive automorphism. Extend $\pi$ by $\pi(0)=0$. Then
--   $$\bar\pi(g)=\pi(\varphi^{-1}g),\qquad (\bar\pi,\pi_0)\text{ is a facet of }P(G,\varphi(g_0)).$$
--   The same real constant is retained. The zero target is included under the published nonzero-solution master convention.
--
--   This records the action of group symmetry on the entire facet family.
--
--   Differences from the source:
--   - encoding: an automorphism and inverse-coordinate action → an additive equivalence and precomposition with its inverse, using ext at zero; reason: the inverse of a nonzero element under an automorphism is nonzero, so the extension has no effect on the coefficients
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 477, THEOREM 14

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Asymptotic.Supplement

theorem theorem_14 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π : Gomory69.Lifting.Plus G → ℝ) (π₀ : ℝ)
    (hface : Gomory69.Lifting.IsFace G g₀ π π₀) (φ : G ≃+ G) :
    Gomory69.Lifting.IsFace G (φ g₀)
      (fun g => Gomory69.Lifting.ext π (φ.symm (g : G))) π₀ := by sorry

end Gomory69.Asymptotic.Supplement
