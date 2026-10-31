-- Prove2me | Theorems.Thm_NashStackelberg_closure_step
-- name    : NashStackelberg.closure_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:31.787412+00:00
-- url     : https://prove2.me/theorems/27715335-0d46-4a20-a9a3-38371fd6fb9c
-- title:
--   pp.13–14 — the best-response inequality extends from $\mathrm{conv}(\mathcal F^i)$ to $\mathrm{cl\,conv}(\mathcal F^i)$
-- statement:
--   Let $N$ be a NASP, $i$ a player and $\tilde x$ a profile. If
--   $$
--   \big(C^i\tilde x^{-i}+c^i\big)^{\!\top}\tilde x^i\le\big(C^i\tilde x^{-i}+c^i\big)^{\!\top}\bar x^i\qquad\text{for every }\bar x^i\in\mathrm{conv}(\mathcal F^i),
--   $$
--   then the same inequality holds for every $\bar x^i\in\mathrm{cl\,conv}(\mathcal F^i)$.
--
--   The right side is continuous in $\bar x^i$, so the inequality passes to limits of convex combinations. Together with (4b) it shows that a player of $\widetilde N$ has no profitable deviation anywhere in its convexified strategy set $\widetilde{\mathcal F}^i=\mathrm{cl\,conv}(\mathcal F^i)$.
--
--   Differences from the source:
--   - generalization: x̃ⁱ the mean of an MNE of N → x̃ an arbitrary profile; reason: the page's profile is a special case
--   - generalization: one leader dimension nℓ and one follower dimension nf for all players (xⁱ ∈ ℝ^{nℓ+nf}) → each player has its own numbers of leader variables, followers and follower variables; reason: the statement specializes to equal dimensions
--   - generalization: Qₖ a positive semi-definite matrix → vᵀQₖv ≥ 0 for all v, Qₖ not required to be symmetric; reason: covers every symmetric PSD matrix; only the quadratic form enters the followers' objectives
--   - encoding: follower constraints y ∈ 𝓕 (𝓕 a polyhedron) and Ax + By ≤ b → one row system Aₖw + Bₖyₖ ≤ bₖ per follower; reason: a polyhedron 𝓕 is a row system with zero w-part; same instances
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, proof of Theorem 4, Statement (ii.), pp.13–14

import Mathlib
import Definitions.Def_NashStackelberg_NASP_Ftilde
import Definitions.Def_NashStackelberg_NASP_cost

namespace NashStackelberg

/-- **The best-response inequality extends from `conv(𝓕ⁱ)` to `cl conv(𝓕ⁱ)`** (Carvalho, Dragotto,
Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, proof of
Theorem 4, Statement (ii.), pp.13–14: "Thus, (Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̃ⁱ ≤ (Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̄ⁱ holds for any
x̄ⁱ ∈ cl conv(𝓕ᵢ)").

Let `N` be a NASP, `i` a player and `x̃` a profile. If
`(Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̃ⁱ ≤ (Cⁱx̃⁻ⁱ + cⁱ)ᵀ x̄ⁱ` for every `x̄ⁱ ∈ conv(𝓕ⁱ)`, then the same inequality holds
for every `x̄ⁱ ∈ cl conv(𝓕ⁱ)`.

**Formalization Note.** `cl conv(𝓕ⁱ)` is `N.Ftilde i = closure (convexHull ℝ (N.F i))`; the
costs are written as in `eq_4b`. -/
theorem closure_step {n : ℕ} (N : NASP n) (i : Fin n) (x : (j : Fin n) → N.Var j → ℝ)
    (h : ∀ x' ∈ convexHull ℝ (N.F i), N.cost i x ≤ N.cost i (Function.update x i x')) :
    ∀ x' ∈ N.Ftilde i, N.cost i x ≤ N.cost i (Function.update x i x') := by sorry

end NashStackelberg
