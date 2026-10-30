-- Prove2me | Theorems.Thm_OnlineCRS_Combine_def_2_10_combination_feasible
-- name    : OnlineCRS.Combine.def_2_10_combination_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:37.893416+00:00
-- url     : https://prove2.me/theorems/427fd514-1810-423b-b2b8-af4dbf6416bd
-- title:
--   Definition 2.10: $P_1\cap P_2$ is a relaxation of the down-closed family $\mathcal F_1\cap\mathcal F_2$
-- statement:
--   Definition 2.10 asserts that the combination of greedy OCRSs for $P_1$ and $P_2$ is a greedy OCRS *for the polytope* $P_1\cap P_2$. By Definition 1.3 this requires $P_1\cap P_2$ to be a relaxation for a down-closed feasible family, namely $\mathcal F_1\cap\mathcal F_2$.
--
--   Let $\mathcal F_1,\mathcal F_2\subseteq 2^N$ be down-closed and let $P_1,P_2\subseteq[0,1]^N$ be relaxations of $P_{\mathcal F_1}$ and $P_{\mathcal F_2}$ (Definition 1.1). Then $\mathcal F_1\cap\mathcal F_2$ is down-closed and
--   $$ (P_1\cap P_2)\cap\{0,1\}^N=P_{\mathcal F_1\cap\mathcal F_2}\cap\{0,1\}^N,\qquad P_1\cap P_2\subseteq[0,1]^N .$$
--
--   This makes the combination of Definition 2.10 a greedy OCRS in the sense of Definition 1.3; it is the first clause of Theorem 1.9.
--
--   **Formalization Note** The part of the claim that the combined family $\mathcal F_{\pi^1,x}\cap\mathcal F_{\pi^2,x}$ is a down-closed subfamily of $\mathcal F_1\cap\mathcal F_2$ is built into the definition of the combination; this theorem is the remaining part.
--
--   Differences from the source:
--   - generalization: P₁, P₂ polytopes → P₁, P₂ arbitrary subsets of [0,1]^N with the {0,1}-point property of Definition 1.1; reason: no step uses that P is a polytope; every polytope relaxation satisfies the hypothesis
--   - reading: P_F = conv({1_F | I ∈ F}) (typo) → P_F = conv{1_I | I ∈ F}; reason: the bound variable is I; the only reading that typechecks, matching 'the convex hull of all characteristic vectors of feasible sets'
--   - encoding: 'the combination of π¹ and π² is a greedy OCRS π for the polytope P = P₁ ∩ P₂' → split into the support property of combine (down-closed subfamilies of F₁ ∩ F₂, in its definition) and this theorem (F₁ ∩ F₂ down-closed, P₁ ∩ P₂ a relaxation of it); reason: Lean structure fields carry the support property; together they are the claim
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 2.10 (unnumbered claim 'is a greedy OCRS π for the polytope P = P1 ∩ P2'), p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_DownClosed
import Definitions.Def_OnlineCRS_Combine_IsRelaxation

namespace OnlineCRS.Combine

/-- **The combination lives on a feasible setting: `P₁ ∩ P₂` is a relaxation of `F₁ ∩ F₂`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 2.10, p. 15 (unnumbered claim): "Given two greedy OCRSs `π¹` and `π²` for polytopes
`P₁` and `P₂`, the combination of `π¹` and `π²` is a greedy OCRS `π` for the polytope
`P = P₁ ∩ P₂`. For every input `x ∈ P`, `π` is defined by the down-closed family
`F_{π,x} = F_{π¹,x} ∩ F_{π²,x}`."

If `F₁, F₂` are down-closed and `P₁, P₂` are relaxations of `P_{F₁}, P_{F₂}`, then `F₁ ∩ F₂` is
down-closed and `P₁ ∩ P₂` is a relaxation of `P_{F₁ ∩ F₂}` (Definition 1.3's setting for the
combination).

**Formalization Note.** Reading 4: `P₁, P₂` are arbitrary subsets of `[0,1]^N` satisfying
Definition 1.1's `{0,1}`-point condition, not necessarily polytopes. -/
theorem def_2_10_combination_feasible {N : Type*} [Fintype N] [DecidableEq N]
    {F₁ F₂ : Finset (Finset N)} {P₁ P₂ : Set (N → ℝ)}
    (hF₁ : DownClosed F₁) (hF₂ : DownClosed F₂)
    (hP₁ : IsRelaxation F₁ P₁) (hP₂ : IsRelaxation F₂ P₂) :
    DownClosed (F₁ ∩ F₂) ∧ IsRelaxation (F₁ ∩ F₂) (P₁ ∩ P₂) := by sorry

end OnlineCRS.Combine
