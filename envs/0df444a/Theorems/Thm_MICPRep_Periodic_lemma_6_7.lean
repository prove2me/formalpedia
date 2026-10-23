-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_7
-- name    : MICPRep.Periodic.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:13.17768+00:00
-- url     : https://prove2.me/theorems/b82d596d-f2a9-4996-ba39-055f5b02a8b4
-- title:
--   Lemma 6.7 (with dim aff_ℤ(I) ≥ 1 added), p. 26 — slicing an index set in a slab into finitely many pieces of lower rational dimension
-- statement:
--   Let $l, u \in \mathbb Z$ and let $I \subseteq \mathbb R^d$ be convex with $\dim \mathrm{aff}_{\mathbb Z}(I) \ge 1$,
--   $$\mathrm{aff}_{\mathbb Z}(I) = \mathbb R^{\dim(\mathrm{aff}_{\mathbb Z}(I))} \times \{0\}^{d - \dim(\mathrm{aff}_{\mathbb Z}(I))} \quad (6.13a), \qquad I_{\mathbb Z} \subseteq \{z : l \le z_1 \le u\} \quad (6.13b).$$
--   Then there are invertible rational affine maps $R_i : \mathbb R^d \to \mathbb R^d$, $i \in [l, u] \cap \mathbb Z$, such that
--   $$\dim \mathrm{aff}_{\mathbb Z}(R_i(I)) \le \dim \mathrm{aff}_{\mathbb Z}(I) - 1, \qquad \bigcup_{i=l}^u \bigl(R_i(I) \cap \mathbb Z^d\bigr) = I \cap \mathbb Z^d, \qquad R_i^{-1}(z) = z \ \ \forall z \in R_i(I) \cap \mathbb Z^d.$$
--
--   The slices replace the naive slices $\{z \in I : z_1 = i\}$, which need not stay rationally unbounded, in the induction step of Lemma 6.1.
--
--   **Formalization Note** The hypothesis $\dim \mathrm{aff}_{\mathbb Z}(I) \ge 1$ is added: when the dimension is $0$, (6.13a) forces $I \cap \mathbb Z^d = \{0\}$, some $R_i(I)$ must then contain an integer point, so its rational affine hull has dimension $\ge 0 > -1$ and (6.14a) fails. Lemma 6.1 uses the lemma only when this dimension is at least $1$. Dimensions are integers with $\dim\emptyset = -1$ (slices without integer points have dimension $-1$). The maps are indexed by all of $\mathbb Z$ and constrained only on $[l,u]$.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 26, Lemma 6.7 (with the hypothesis dim aff_ℤ(I) ≥ 1 added)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.7, p. 26, with `dim aff_ℤ(I) ≥ 1` added. -/
theorem lemma_6_7 {d : ℕ} (l u : ℤ) (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (h613a : (affZ I : Set (Fin d → ℝ)) = coordSubspace d (affDim (affZ I)))
    (h613b : IZ I ⊆ slab d l u) (hdim : 1 ≤ affDim (affZ I)) :
    ∃ (A : ℤ → Matrix (Fin d) (Fin d) ℚ) (b : ℤ → Fin d → ℚ),
      (∀ i ∈ Set.Icc l u, IsUnit (A i)) ∧
      (∀ i ∈ Set.Icc l u, affDim (affZ (ratAff (A i) (b i) '' I)) ≤ affDim (affZ I) - 1) ∧
      (⋃ i ∈ Set.Icc l u, ratAff (A i) (b i) '' I ∩ intLattice d) = I ∩ intLattice d ∧
      ∀ i ∈ Set.Icc l u, ∀ z ∈ ratAff (A i) (b i) '' I ∩ intLattice d,
        ratAffInv (A i) (b i) z = z := by sorry

end MICPRep.Periodic
