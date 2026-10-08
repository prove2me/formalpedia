-- Prove2me | Theorems.Thm_GivenDegreeSeq_Interior_proposition_1_2
-- name    : GivenDegreeSeq.Interior.proposition_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:44.359974+00:00
-- url     : https://prove2.me/theorems/732d7283-f084-497c-b9af-070467eb1a2f
-- title:
--   Proposition 1.2 — the interior of the set of degree-sequence scaling limits
-- statement:
--   Let $f:[0,1]\to[0,1]$ be a function in $D'[0,1]$ (nonincreasing, left continuous on $(0,1)$). Then $f$ belongs to the interior of $\mathcal F$ — the set of scaling limits of degree sequences, with the topology of the modified $L^1$ norm $\|\cdot\|_{1'}$ on $D'[0,1]$ — if and only if:
--
--   1. there are two constants $c_1>0$ and $c_2<1$ such that $c_1\le f(x)\le c_2$ for all $x\in[0,1]$, and
--   2. for each $x\in(0,1]$,
--   $$\int_x^1\min\{f(y),x\}\,dy+x^2-\int_0^x f(y)\,dy>0.$$
--
--   Condition (ii) is a continuum version of the Erdős–Gallai criterion. The interior of $\mathcal F$ is exactly the hypothesis of the paper's Theorem 1.1 (convergence of uniform random graphs with a given degree sequence to an explicit graph limit), so this proposition makes that hypothesis checkable.
--
--   **Formalization Note** $f$ is `ℝ → ℝ`, with hypotheses only on $[0,1]$. The hypothesis $f([0,1])\subseteq[0,1]$ is kept as on the page, although the "only if" direction makes it redundant. The interior is the ball formulation in $(D'[0,1],\|\cdot\|_{1'})$, defined in `ScalingLimit`.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 5, Proposition 1.2 (proof §5, pp. 23–25)

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit

namespace GivenDegreeSeq.Interior

/-- **Proposition 1.2** (p. 5). A function `f : [0,1] → [0,1]` in `D′[0,1]` belongs to the
interior of `F` (for the modified `L¹` norm `‖·‖_{1′}`) if and only if
(i) there are constants `c₁ > 0` and `c₂ < 1` with `c₁ ≤ f(x) ≤ c₂` for all `x ∈ [0,1]`, and
(ii) for each `x ∈ (0,1]`, `∫ₓ¹ min{f(y), x} dy + x² − ∫₀ˣ f(y) dy > 0`. -/
theorem proposition_1_2 (f : ℝ → ℝ) (hf : InDprime f)
    (hrange : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc (0 : ℝ) 1) :
    InteriorF f ↔
      ((∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₂ < 1 ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, c₁ ≤ f x ∧ f x ≤ c₂) ∧
        ∀ x ∈ Set.Ioc (0 : ℝ) 1,
          0 < (∫ y in x..1, min (f y) x) + x ^ 2 - ∫ y in (0 : ℝ)..x, f y) := by sorry

end GivenDegreeSeq.Interior
