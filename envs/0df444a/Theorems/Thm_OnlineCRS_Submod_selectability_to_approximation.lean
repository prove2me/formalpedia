-- Prove2me | Theorems.Thm_OnlineCRS_Submod_selectability_to_approximation
-- name    : OnlineCRS.Submod.selectability_to_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:26.345656+00:00
-- url     : https://prove2.me/theorems/58a4236e-ffc1-4310-ab9c-f1c9f515255b
-- title:
--   Theorem 1.10, p. 5 (restated p. 16) — a (b, c)-selectable greedy OCRS gives E[f(S)] ≥ c·F(x), and E[f(S(1/2))] ≥ (c/4)·F(x) for non-monotone f
-- statement:
--   Let $N$ be a finite ground set, $\mathcal F\subseteq 2^N$ a down-closed family of feasible sets and $P\subseteq[0,1]^N$ a relaxation of it. Let $b,c\in[0,1]$, let $\pi$ be a $(b,c)$-selectable greedy OCRS for $P$ (deterministic or randomized), and let $x\in bP$. Let $f:2^N\to\mathbb R_{\ge0}$ be non-negative and submodular, with multilinear extension $F(x)=\mathbb E[f(R(x))]$. The elements arrive in an order chosen by the **almighty adversary**, who knows the realized active set $R(x)$ and the realized family $\mathcal F_x$ before choosing it.
--
--   1. If $f$ is moreover monotone, the set $S$ selected by $\pi$ satisfies
--   $$\mathbb E[f(S)]\ge c\cdot F(x).$$
--   2. Even if $f$ is not monotone, let $S(1/2)$ contain every element of $S$ independently with probability $1/2$, the coins being part of the algorithm and known to the adversary. Then
--   $$\mathbb E[f(S(1/2))]\ge \frac c4\cdot F(x).$$
--
--   The theorem turns any selectability guarantee into an approximation guarantee for online submodular maximization, losing only the factor $c$ for monotone objectives and $c/4$ in general. It is how the paper derives its applications to prophet inequalities and Bayesian mechanism design from the OCRSs for matroids, matchings and knapsacks.
--
--   **Formalization Note** A deterministic greedy OCRS is the special case of a point-mass family distribution. The adversary is a function from all realized randomness (family, active set, and in part 2 the coins $C$, with $S(1/2)=S\cap C$) to arrival orders. The standing assumptions of Definition 1.3 (a down-closed $\mathcal F$, $P\subseteq[0,1]^N$ a relaxation of $P_{\mathcal F}$, $b,c\in[0,1]$) are explicit hypotheses. Monotonicity is $A\subseteq B\Rightarrow f(A)\le f(B)$ (footnote 6) and submodularity is $f(A\cup B)+f(A\cap B)\le f(A)+f(B)$ (footnote 5).
-- source:
--   arXiv:1508.00142v2, Theorem 1.10, p. 5; restatement, p. 16

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model

open scoped Pointwise

namespace OnlineCRS.Submod

/-- Theorem 1.10 (arXiv:1508.00142v2, p. 5, restated p. 16): let `P ⊆ [0,1]^N` be a relaxation of the
down-closed feasible sets `𝓕`, `w` a `(b, c)`-selectable (randomized) greedy OCRS for `P`, `x ∈ bP`, and
`f ≥ 0` submodular with multilinear extension `F`. Against every almighty adversary:
(i) if `f` is monotone, the selected set `S` satisfies `E[f(S)] ≥ c · F(x)`;
(ii) without monotonicity, `E[f(S(1/2))] ≥ (c/4) · F(x)`, where the coins defining `S(1/2)` are known to
the adversary. -/
theorem selectability_to_approximation {α : Type} [Fintype α] [DecidableEq α]
    (𝓕 : Finset α → Prop) (P : Set (α → ℝ))
    (hPoly : IsPolytope P) (hRel : IsRelaxation 𝓕 P)
    (b c : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (hw : OnlineCRS.Matroid.IsSelectableRand 𝓕 P b c w)
    (x : α → ℝ) (hx : x ∈ b • P)
    (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ((∀ A B : Finset α, A ⊆ B → f A ≤ f B) →
        ∀ ord : Finset (Finset α) → Finset α → List α, (∀ Fam A, IsOrder (ord Fam A)) →
          c * NonmonotoneSubmod.Shared.F f x ≤ expOutput w x ord f) ∧
      (∀ ord : Finset (Finset α) → Finset α → Finset α → List α,
        (∀ Fam A C, IsOrder (ord Fam A C)) →
          c / 4 * NonmonotoneSubmod.Shared.F f x ≤ expOutputHalf w x ord f) := by sorry

end OnlineCRS.Submod
