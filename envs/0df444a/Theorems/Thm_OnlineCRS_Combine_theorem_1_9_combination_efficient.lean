-- Prove2me | Theorems.Thm_OnlineCRS_Combine_theorem_1_9_combination_efficient
-- name    : OnlineCRS.Combine.theorem_1_9_combination_efficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:30:01.120823+00:00
-- url     : https://prove2.me/theorems/06cd1a8b-c6bc-4813-aae4-6b3650240d53
-- title:
--   Theorem 1.9 (efficiency clause): the combination is efficient if both OCRSs are
-- statement:
--   Consider families of instances $i$, instance $i$ having ground set $\{0,\dots,n_i-1\}$ and description $\mathrm{code}_i$, with greedy OCRSs $\pi^1_i$ for $\mathcal F_{1,i}$ and $\pi^2_i$ for $\mathcal F_{2,i}$ and sets $P_{1,i},P_{2,i}$. If the family $(\pi^1_i)$ is efficient for $(P_{1,i})$ and $(\pi^2_i)$ is efficient for $(P_{2,i})$ (Definition 1.7), then the family of combinations $(\pi_i)$ (Definition 2.10) is efficient for $(P_{1,i}\cap P_{2,i})$.
--
--   This is the second sentence of Theorem 1.9, for the combination that the first sentence uses; the paper gives no proof.
--
--   Differences from the source:
--   - reading: 'a polynomial time algorithm that, for a given input x, samples an efficient independence oracle' → polynomial-time Turing machines (Mathlib TM2ComputableInPolyTime) on a fixed binary encoding: one computes m(i, x), r is uniform on {0,…,m}, the other decides D(i, x, r, S); the law of {S | D} equals the law of F_{π,x} for rational x ∈ P; reason: Definition 1.7 fixes no machine model; rational inputs because inputs are finite; a uniform range rather than fair coins because the paper calls its rational-bias knapsack OCRS efficient
--   - generalization: one polytope P with its OCRS → families of instances i (ground set Fin (n i), description code i) with one machine pair for the whole family; reason: polynomial time is only meaningful as instances grow; the one-element index set ι = Unit is the paper's single instance
--   - generalization: π¹, π² (b, c₁)-, (b, c₂)-selectable greedy OCRSs for relaxations P₁, P₂ of down-closed families → no selectability, relaxation or down-closedness hypotheses; reason: efficiency of the combination does not depend on them; the source's case satisfies the weaker hypotheses
--   - reading: F_{π,x} = F_{π¹,x} ∩ F_{π²,x}, coupling unspecified → F_{π¹,x} and F_{π²,x} drawn independently; reason: under an arbitrary coupling Lemma 2.11 is false (N = {e, f}, both OCRSs (1, 1/2)-selectable, anti-coupled intersection never selects e at x = (1, 1)); the independent coupling is the one the FKG step needs
--   - encoding: F_{π,x} defined for x ∈ P → the law of F_{π,x} is defined for every x ∈ ℝ^N; reason: a paper OCRS extends to all x (e.g. F_x = {∅}); only x ∈ b·P and x ∈ P are ever evaluated
--   - reading: a down-closed subfamily F_{π,x} ⊆ F → a down-closed subfamily F_{π,x} ⊆ F that contains ∅; reason: the greedy rule starts from the empty selection and the paper reads selectability as a guarantee that e is selected with probability ≥ c (p. 3); the empty family would make every element vacuously selectable (χ_e(A, ∅, ∅) holds) while selecting nothing, and would witness Theorem 1.9's existential trivially
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Theorem 1.9 (second sentence 'Moreover, the last greedy OCRS is efficient if π1 and π2 are'), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS
import Definitions.Def_OnlineCRS_Combine_combine
import Definitions.Def_OnlineCRS_Combine_IsEfficient

namespace OnlineCRS.Combine

/-- **Theorem 1.9, efficiency clause: the combination is efficient if both OCRSs are.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Theorem 1.9, p. 4 (second sentence; the paper gives no proof): "Moreover, the last greedy
OCRS is efficient if `π¹` and `π²` are."

For instance families (instance `i` on ground set `Fin (n i)`, described by `code i`), if `π₁` is
efficient for `P₁` and `π₂` is efficient for `P₂`, then `i ↦ combine (π₁ i) (π₂ i)` is efficient
for `i ↦ P₁ i ∩ P₂ i`.

**Formalization Note.** Efficiency is Definition 1.7 in Reading 6 (Turing machines, rational
inputs, a uniform draw from a computed range, instance families; `ι = Unit` is a single
instance). No down-closedness, relaxation or selectability hypothesis is needed, so none is
assumed (generalization). -/
theorem theorem_1_9_combination_efficient {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    {F₁ F₂ : ∀ i, Finset (Finset (Fin (n i)))} (P₁ P₂ : ∀ i, Set (Fin (n i) → ℝ))
    (π₁ : ∀ i, GreedyOCRS (F₁ i)) (π₂ : ∀ i, GreedyOCRS (F₂ i))
    (h₁ : IsEfficient n code P₁ π₁) (h₂ : IsEfficient n code P₂ π₂) :
    IsEfficient n code (fun i => P₁ i ∩ P₂ i) (fun i => combine (π₁ i) (π₂ i)) := by sorry

end OnlineCRS.Combine
