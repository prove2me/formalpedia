-- Prove2me | Theorems.Thm_OnlineCRS_Combine_theorem_1_9_combine_greedy_ocrs
-- name    : OnlineCRS.Combine.theorem_1_9_combine_greedy_ocrs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:31:11.552777+00:00
-- url     : https://prove2.me/theorems/36f5761a-c4b3-46e3-b0e7-4a5ef8fae9ae
-- title:
--   Theorem 1.9: greedy OCRSs for $P_1$ and $P_2$ combine into a $(b,c_1c_2)$-selectable greedy OCRS for $P_1\cap P_2$, efficient if both are
-- statement:
--   Let $b,c_1,c_2\in[0,1]$. If $\pi^1$ is a $(b,c_1)$-selectable greedy OCRS for a relaxation $P_1$ of a down-closed family $\mathcal F_1$, and $\pi^2$ is a $(b,c_2)$-selectable greedy OCRS for a relaxation $P_2$ of a down-closed family $\mathcal F_2$, then
--   1. $P_1\cap P_2$ is a relaxation of the down-closed family $\mathcal F_1\cap\mathcal F_2$, and
--   2. there exists a greedy OCRS $\pi$ for $P_1\cap P_2$ that is $(b,c_1\cdot c_2)$-selectable, and that is efficient (Definition 1.7) whenever $\pi^1$ and $\pi^2$ are.
--
--   The statement is made uniformly for a family of instances $i$ (ground set $\{0,\dots,n_i-1\}$, description $\mathrm{code}_i$, data $\mathcal F_{j,i},P_{j,i},\pi^j_i$), with one family $(\pi_i)$ satisfying both conclusions: $(b,c_1c_2)$-selectable for $P_{1,i}\cap P_{2,i}$ for every $i$, and efficient as a family whenever $(\pi^1_i)$ and $(\pi^2_i)$ are.
--
--   Applied repeatedly to the matroid, matching and knapsack OCRSs of Theorem 1.8, this gives constant-selectability greedy OCRSs for intersections of a constant number of such constraints, which feed the paper's prophet inequalities and posted-price mechanisms.
--
--   **Formalization Note** Clause 1 is Definition 1.3's requirement, contained in "a greedy OCRS for the polytope $P_1\cap P_2$", that $P_1\cap P_2$ is a relaxation of a down-closed feasible family.
--
--   Differences from the source:
--   - generalization: one polytope P with its OCRS → families of instances i (ground set Fin (n i), description code i) with one machine pair for the whole family; reason: polynomial time is only meaningful as instances grow; the one-element index set ι = Unit is the paper's single instance
--   - generalization: P₁, P₂ polytopes → P₁, P₂ arbitrary subsets of [0,1]^N with the {0,1}-point property of Definition 1.1; reason: no step uses that P is a polytope; every polytope relaxation satisfies the hypothesis
--   - reading: P_F = conv({1_F | I ∈ F}) (typo) → P_F = conv{1_I | I ∈ F}; reason: the bound variable is I; the only reading that typechecks, matching 'the convex hull of all characteristic vectors of feasible sets'
--   - reading: a greedy OCRS defines F_{π,x}, possibly at random; probability over R(x) and the random choice of F_x → a greedy OCRS is the law of F_{π,x}, a distribution depending on x only, independent of R(x); reason: F_x is fixed before any element is revealed (Definition 1.3, paragraph after Definition 1.4)
--   - encoding: F_{π,x} defined for x ∈ P → the law of F_{π,x} is defined for every x ∈ ℝ^N; reason: a paper OCRS extends to all x (e.g. F_x = {∅}); only x ∈ b·P and x ∈ P are ever evaluated
--   - reading: 'a polynomial time algorithm that, for a given input x, samples an efficient independence oracle' → polynomial-time Turing machines (Mathlib TM2ComputableInPolyTime) on a fixed binary encoding: one computes m(i, x), r is uniform on {0,…,m}, the other decides D(i, x, r, S); the law of {S | D} equals the law of F_{π,x} for rational x ∈ P; reason: Definition 1.7 fixes no machine model; rational inputs because inputs are finite; a uniform range rather than fair coins because the paper calls its rational-bias knapsack OCRS efficient
--   - reading: a down-closed subfamily F_{π,x} ⊆ F → a down-closed subfamily F_{π,x} ⊆ F that contains ∅; reason: the greedy rule starts from the empty selection and the paper reads selectability as a guarantee that e is selected with probability ≥ c (p. 3); the empty family would make every element vacuously selectable (χ_e(A, ∅, ∅) holds) while selecting nothing, and would witness Theorem 1.9's existential trivially
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Theorem 1.9, p. 4; proof via Lemma 2.11, p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_DownClosed
import Definitions.Def_OnlineCRS_Combine_IsRelaxation
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS
import Definitions.Def_OnlineCRS_Combine_IsSelectable
import Definitions.Def_OnlineCRS_Combine_IsEfficient

namespace OnlineCRS.Combine

/-- **Theorem 1.9: greedy OCRSs combine under intersection, preserving efficiency.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Theorem 1.9, p. 4: "If `π¹` is a `(b, c₁)`-selectable greedy OCRS for a polytope `P₁`, and
`π²` is a `(b, c₂)`-selectable greedy OCRS for a polytope `P₂`, then there exists a
`(b, c₁ · c₂)`-selectable greedy OCRS for the polytope `P₁ ∩ P₂`. Moreover, the last greedy OCRS is
efficient if `π¹` and `π²` are."

For a family of instances `i` (ground set `Fin (n i)`, description `code i`) with down-closed
`F₁ i, F₂ i`, relaxations `P₁ i, P₂ i`, `b, c₁, c₂ ∈ [0,1]`, and greedy OCRSs `π₁ i, π₂ i` that are
`(b, c₁)`- resp. `(b, c₂)`-selectable: `P₁ i ∩ P₂ i` is a relaxation of the down-closed family
`F₁ i ∩ F₂ i`, and there is one family of greedy OCRSs `π i` for `F₁ i ∩ F₂ i` that is
`(b, c₁ c₂)`-selectable for `P₁ i ∩ P₂ i` for every `i`, and efficient whenever `π₁` and `π₂` are.

**Formalization Note.**
* Reading 8: "greedy OCRS for the polytope `P₁ ∩ P₂`" includes Definition 1.3's requirement that
  `P₁ ∩ P₂` is a relaxation of a down-closed family (here `F₁ ∩ F₂`); this is the first conjunct.
* Reading 6: efficiency (Definition 1.7) in the Turing-machine model, stated for instance families
  (generalization; `ι = Unit` is the paper's single instance).
* Reading 4: polytopes generalized to subsets of `[0,1]^N`. Greedy OCRSs may be randomized
  (Reading 2). One common `b`, as in the theorem. -/
theorem theorem_1_9_combine_greedy_ocrs {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    (F₁ F₂ : ∀ i, Finset (Finset (Fin (n i)))) (P₁ P₂ : ∀ i, Set (Fin (n i) → ℝ))
    (hF₁ : ∀ i, DownClosed (F₁ i)) (hF₂ : ∀ i, DownClosed (F₂ i))
    (hP₁ : ∀ i, IsRelaxation (F₁ i) (P₁ i)) (hP₂ : ∀ i, IsRelaxation (F₂ i) (P₂ i))
    (b c₁ c₂ : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc₁ : c₁ ∈ Set.Icc (0 : ℝ) 1) (hc₂ : c₂ ∈ Set.Icc (0 : ℝ) 1)
    (π₁ : ∀ i, GreedyOCRS (F₁ i)) (π₂ : ∀ i, GreedyOCRS (F₂ i))
    (h₁ : ∀ i, IsSelectable (P₁ i) (π₁ i) b c₁) (h₂ : ∀ i, IsSelectable (P₂ i) (π₂ i) b c₂) :
    (∀ i, DownClosed (F₁ i ∩ F₂ i) ∧ IsRelaxation (F₁ i ∩ F₂ i) (P₁ i ∩ P₂ i)) ∧
      ∃ π : ∀ i, GreedyOCRS (F₁ i ∩ F₂ i),
        (∀ i, IsSelectable (P₁ i ∩ P₂ i) (π i) b (c₁ * c₂)) ∧
        (IsEfficient n code P₁ π₁ → IsEfficient n code P₂ π₂ →
          IsEfficient n code (fun i => P₁ i ∩ P₂ i) π) := by sorry

end OnlineCRS.Combine
