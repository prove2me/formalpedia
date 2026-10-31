-- Prove2me | Theorems.Thm_NashStackelberg_statement_i
-- name    : NashStackelberg.statement_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:57.46062+00:00
-- url     : https://prove2.me/theorems/f92e7208-785b-455c-8aed-255f50ad2cff
-- title:
--   Statement (i.), pp.12–13 — a PNE of $\widetilde N$ split into lotteries over $\mathcal F^i$ is an MNE of $N$
-- statement:
--   Let $N$ be a NASP and let $\tilde x$ be a pure Nash equilibrium of the convexified game $\widetilde N$, in which player $i$ minimizes the same cost over $\mathrm{cl\,conv}(\mathcal F^i)$. For every player $i$ let $(\hat x^i,p^i)$ be a finite lottery with
--   $$
--   p^i_j\ge0,\qquad\sum_j p^i_j=1,\qquad \hat x^i_j\in\mathcal F^i\ \text{ whenever } p^i_j>0,\qquad \sum_j p^i_j\,\hat x^i_j=\tilde x^i .
--   $$
--   Then the profile in which every player $i$ independently plays $\hat x^i_j$ with probability $p^i_j$ is a mixed Nash equilibrium of $N$.
--
--   This is the soundness half of Theorem 4: whatever lotteries Steps 6–7 of Algorithm 1 produce from the equilibrium found in Step 4, they form an MNE of the original non-convex game.
--
--   Differences from the source:
--   - generalization: the lotteries (x̂ⁱ, pⁱ) returned by Algorithm 1 → any PNE x̃ of Ñ and any finite lotteries with mean x̃ⁱ; reason: Steps 6 and 7 return such lotteries
--   - generalization: x̂ⁱⱼ ∈ 𝓕ⁱ for every j → x̂ⁱⱼ ∈ 𝓕ⁱ only when pⁱⱼ ≠ 0; reason: points of probability zero carry no mass; the page's case is included
--   - generalization: one leader dimension nℓ and one follower dimension nf for all players (xⁱ ∈ ℝ^{nℓ+nf}) → each player has its own numbers of leader variables, followers and follower variables; reason: the statement specializes to equal dimensions
--   - generalization: Qₖ a positive semi-definite matrix → vᵀQₖv ≥ 0 for all v, Qₖ not required to be symmetric; reason: covers every symmetric PSD matrix; only the quadratic form enters the followers' objectives
--   - encoding: follower constraints y ∈ 𝓕 (𝓕 a polyhedron) and Ax + By ≤ b → one row system Aₖw + Bₖyₖ ≤ bₖ per follower; reason: a polyhedron 𝓕 is a row system with zero w-part; same instances
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, proof of Theorem 4, Statement (i.), pp.12–13

import Mathlib
import Definitions.Def_NashStackelberg_IsPNE
import Definitions.Def_NashStackelberg_IsMNE
import Definitions.Def_NashStackelberg_NASP_Ftilde
import Definitions.Def_NashStackelberg_NASP_cost
import Definitions.Def_NashStackelberg_Lottery_measure

namespace NashStackelberg

/-- **A PNE of `Ñ` decomposed into lotteries over `𝓕ⁱ` is an MNE of `N`** (Carvalho, Dragotto,
Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, proof of
Theorem 4, Statement (i.), pp.12–13).

Let `x̃` be a PNE of the convexified game `Ñ` (strategy sets `cl conv 𝓕ⁱ`, the costs of `N`), and
for every player `i` let `(x̂ⁱ, pⁱ)` be a finite lottery with `pⁱⱼ ≥ 0`, `Σⱼ pⁱⱼ = 1`, every point
of positive probability in `𝓕ⁱ`, and mean `Σⱼ pⁱⱼ x̂ⁱⱼ = x̃ⁱ`. Then the profile in which each player
`i` independently plays `x̂ⁱⱼ` with probability `pⁱⱼ` is an MNE of `N`.

**Formalization Note.** Points of probability zero are not required to lie in `𝓕ⁱ` (they carry
no mass); this covers Step 6's one-point lottery and Step 7's convex combination. -/
theorem statement_i {n : ℕ} (N : NASP n) (x : (i : Fin n) → N.Var i → ℝ)
    (hx : IsPNE N.Ftilde N.cost x) (L : (i : Fin n) → Lottery (N.Var i))
    (hpts : ∀ i j, (L i).prob j ≠ 0 → (L i).pts j ∈ N.F i)
    (hprob : ∀ i j, 0 ≤ (L i).prob j) (hsum : ∀ i, ∑ j, (L i).prob j = 1)
    (hmean : ∀ i, ∑ j, (L i).prob j • (L i).pts j = x i) :
    IsMNE N.F N.cost (fun i => (L i).measure) := by sorry

end NashStackelberg
