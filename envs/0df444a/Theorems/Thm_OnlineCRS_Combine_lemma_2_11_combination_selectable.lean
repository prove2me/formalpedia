-- Prove2me | Theorems.Thm_OnlineCRS_Combine_lemma_2_11_combination_selectable
-- name    : OnlineCRS.Combine.lemma_2_11_combination_selectable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:28:39.327816+00:00
-- url     : https://prove2.me/theorems/dd104976-a89a-4b53-b9c0-bfcdb60d39ee
-- title:
--   Lemma 2.11: the combination is $(b,c_1c_2)$-selectable
-- statement:
--   Let $\mathcal F_1,\mathcal F_2\subseteq 2^N$ be down-closed, let $P_1,P_2$ be relaxations of $P_{\mathcal F_1},P_{\mathcal F_2}$, and let $b,c_1,c_2\in[0,1]$. If $\pi^1$ is a $(b,c_1)$-selectable greedy OCRS for $P_1$ and $\pi^2$ is a $(b,c_2)$-selectable greedy OCRS for $P_2$, then their combination $\pi$ (Definition 2.10) is $(b,c_1\cdot c_2)$-selectable for $P_1\cap P_2$: for every $x\in b\cdot(P_1\cap P_2)$ and every $e\in N$,
--   $$\Pr\bigl[I\cup\{e\}\in\mathcal F_{\pi^1,x}\cap\mathcal F_{\pi^2,x}\ \ \forall I\subseteq R(x),\ I\in\mathcal F_{\pi^1,x}\cap\mathcal F_{\pi^2,x}\bigr]\ \ge\ c_1\cdot c_2 .$$
--
--   This is the selectability half of Theorem 1.9.
--
--   Differences from the source:
--   - generalization: P₁, P₂ polytopes → P₁, P₂ arbitrary subsets of [0,1]^N with the {0,1}-point property of Definition 1.1; reason: no step uses that P is a polytope; every polytope relaxation satisfies the hypothesis
--   - reading: a greedy OCRS defines F_{π,x}, possibly at random; probability over R(x) and the random choice of F_x → a greedy OCRS is the law of F_{π,x}, a distribution depending on x only, independent of R(x); reason: F_x is fixed before any element is revealed (Definition 1.3, paragraph after Definition 1.4)
--   - reading: F_{π,x} = F_{π¹,x} ∩ F_{π²,x}, coupling unspecified → F_{π¹,x} and F_{π²,x} drawn independently; reason: under an arbitrary coupling Lemma 2.11 is false (N = {e, f}, both OCRSs (1, 1/2)-selectable, anti-coupled intersection never selects e at x = (1, 1)); the independent coupling is the one the FKG step needs
--   - encoding: F_{π,x} defined for x ∈ P → the law of F_{π,x} is defined for every x ∈ ℝ^N; reason: a paper OCRS extends to all x (e.g. F_x = {∅}); only x ∈ b·P and x ∈ P are ever evaluated
--   - reading: a down-closed subfamily F_{π,x} ⊆ F → a down-closed subfamily F_{π,x} ⊆ F that contains ∅; reason: the greedy rule starts from the empty selection and the paper reads selectability as a guarantee that e is selected with probability ≥ c (p. 3); the empty family would make every element vacuously selectable (χ_e(A, ∅, ∅) holds) while selecting nothing, and would witness Theorem 1.9's existential trivially
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Lemma 2.11, p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_DownClosed
import Definitions.Def_OnlineCRS_Combine_IsRelaxation
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS
import Definitions.Def_OnlineCRS_Combine_IsSelectable
import Definitions.Def_OnlineCRS_Combine_combine

namespace OnlineCRS.Combine

/-- **Lemma 2.11: the combination is `(b, c₁ · c₂)`-selectable.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Lemma 2.11, p. 15: "Let `π¹` and `π²` be `(b, c₁)`-selectable and `(b, c₂)`-selectable
greedy OCRSs, respectively. The combination of `π¹` and `π²` is `(b, c₁ · c₂)`-selectable."

Let `F₁, F₂` be down-closed, `P₁, P₂` relaxations of `P_{F₁}, P_{F₂}`, `b, c₁, c₂ ∈ [0,1]`, and
`π₁, π₂` greedy OCRSs for `F₁, F₂` that are `(b, c₁)`-selectable for `P₁` and `(b, c₂)`-selectable
for `P₂`. Then `combine π₁ π₂` is `(b, c₁ c₂)`-selectable for `P₁ ∩ P₂`.

**Formalization Note.** `combine` draws the two families independently (Reading 3); polytopes are
generalized to subsets of the cube (Reading 4). -/
theorem lemma_2_11_combination_selectable {N : Type*} [Fintype N] [DecidableEq N]
    {F₁ F₂ : Finset (Finset N)} {P₁ P₂ : Set (N → ℝ)}
    (hF₁ : DownClosed F₁) (hF₂ : DownClosed F₂)
    (hP₁ : IsRelaxation F₁ P₁) (hP₂ : IsRelaxation F₂ P₂)
    {b c₁ c₂ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc₁ : c₁ ∈ Set.Icc (0 : ℝ) 1) (hc₂ : c₂ ∈ Set.Icc (0 : ℝ) 1)
    (π₁ : GreedyOCRS F₁) (π₂ : GreedyOCRS F₂)
    (h₁ : IsSelectable P₁ π₁ b c₁) (h₂ : IsSelectable P₂ π₂ b c₂) :
    IsSelectable (P₁ ∩ P₂) (combine π₁ π₂) b (c₁ * c₂) := by sorry

end OnlineCRS.Combine
