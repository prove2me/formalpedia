-- Prove2me | Theorems.Thm_NashStackelberg_eq_4b
-- name    : NashStackelberg.eq_4b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:13.173129+00:00
-- url     : https://prove2.me/theorems/5771f341-2e85-461e-b6ff-fb5857551a53
-- title:
--   (4b), p.13 — the best-response inequality extends from $\mathcal F^i$ to $\mathrm{conv}(\mathcal F^i)$
-- statement:
--   Let $N$ be a NASP, $i$ a player and $\tilde x$ a profile. If
--   $$
--   \big(C^i\tilde x^{-i}+c^i\big)^{\!\top}\tilde x^i\le\big(C^i\tilde x^{-i}+c^i\big)^{\!\top}\bar x^i\qquad\text{for every }\bar x^i\in\mathcal F^i,
--   $$
--   then the same inequality holds for every $\bar x^i\in\mathrm{conv}(\mathcal F^i)$.
--
--   The left side is player $i$'s cost at $\tilde x$ and the right side its cost after deviating to $\bar x^i$. Because the cost is linear in the deviation, an inequality valid at every point of $\mathcal F^i$ survives convex combinations; this is the first step in showing that the means of an MNE of $N$ form a PNE of $\widetilde N$.
--
--   Differences from the source:
--   - generalization: x̃ⁱ = Σⱼ pⁱⱼ x̂ⁱⱼ the mean of an MNE of N → x̃ an arbitrary profile; reason: the page's profile is a special case
--   - generalization: one leader dimension nℓ and one follower dimension nf for all players (xⁱ ∈ ℝ^{nℓ+nf}) → each player has its own numbers of leader variables, followers and follower variables; reason: the statement specializes to equal dimensions
--   - generalization: Qₖ a positive semi-definite matrix → vᵀQₖv ≥ 0 for all v, Qₖ not required to be symmetric; reason: covers every symmetric PSD matrix; only the quadratic form enters the followers' objectives
--   - encoding: follower constraints y ∈ 𝓕 (𝓕 a polyhedron) and Ax + By ≤ b → one row system Aₖw + Bₖyₖ ≤ bₖ per follower; reason: a polyhedron 𝓕 is a row system with zero w-part; same instances
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, proof of Theorem 4, Statement (ii.), (4b), p.13

import Mathlib
import Definitions.Def_NashStackelberg_NASP_F
import Definitions.Def_NashStackelberg_NASP_cost

namespace NashStackelberg

/-- **The best-response inequality extends from `𝓕ⁱ` to `conv(𝓕ⁱ)`** (Carvalho, Dragotto,
Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, proof of
Theorem 4, Statement (ii.), (4b), p.13: "First, the inequality holds for any x̄ⁱ ∈ conv(𝓕ᵢ)").

Let `N` be a NASP, `i` a player and `x̃` a profile. If
`(Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̃ⁱ ≤ (Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̄ⁱ` for every `x̄ⁱ ∈ 𝓕ⁱ`, then the same inequality holds for
every `x̄ⁱ ∈ conv(𝓕ⁱ)`.

**Formalization Note.** `(Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̄ⁱ` is `N.cost i (x̃ with xⁱ replaced by x̄ⁱ)`, and
`(Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̃ⁱ` is `N.cost i x̃`. `x̃ⁱ` itself is arbitrary (on the page it is a mean). -/
theorem eq_4b {n : ℕ} (N : NASP n) (i : Fin n) (x : (j : Fin n) → N.Var j → ℝ)
    (h : ∀ x' ∈ N.F i, N.cost i x ≤ N.cost i (Function.update x i x')) :
    ∀ x' ∈ convexHull ℝ (N.F i), N.cost i x ≤ N.cost i (Function.update x i x') := by sorry

end NashStackelberg
