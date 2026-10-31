-- Prove2me | Theorems.Thm_NashStackelberg_statement_ii
-- name    : NashStackelberg.statement_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:54.510835+00:00
-- url     : https://prove2.me/theorems/eb305a15-45f5-40d7-9185-54803e2fb451
-- title:
--   Statement (ii.), pp.13–14 — the means of an MNE of $N$ form a PNE of $\widetilde N$
-- statement:
--   Let $N$ be a NASP and let $\sigma=(\sigma^1,\dots,\sigma^n)$ be a mixed Nash equilibrium of $N$ in which every mixed strategy $\sigma^i$ has a finite first moment. Then the profile of means
--   $$
--   \tilde x^i=\mathbb E_{X^i\sim\sigma^i}\big[X^i\big],\qquad i=1,\dots,n,
--   $$
--   is a pure Nash equilibrium of the convexified game $\widetilde N$: every $\tilde x^i$ lies in $\mathrm{cl\,conv}(\mathcal F^i)$, and no player can lower its cost by a unilateral deviation within $\mathrm{cl\,conv}(\mathcal F^i)$.
--
--   This is the completeness half of Theorem 4, in contrapositive form: if $\widetilde N$ has no PNE, then $N$ has no MNE, so the answer `no` of Algorithm 1 is correct.
--
--   Differences from the source:
--   - generalization: an MNE with finite support (p.11 restricts attention to MNEs over finitely many pure strategies) → any MNE whose mixed strategies have finite first moments; reason: every finite-support MNE is one
--   - generalization: one leader dimension nℓ and one follower dimension nf for all players (xⁱ ∈ ℝ^{nℓ+nf}) → each player has its own numbers of leader variables, followers and follower variables; reason: the statement specializes to equal dimensions
--   - generalization: Qₖ a positive semi-definite matrix → vᵀQₖv ≥ 0 for all v, Qₖ not required to be symmetric; reason: covers every symmetric PSD matrix; only the quadratic form enters the followers' objectives
--   - encoding: follower constraints y ∈ 𝓕 (𝓕 a polyhedron) and Ax + By ≤ b → one row system Aₖw + Bₖyₖ ≤ bₖ per follower; reason: a polyhedron 𝓕 is a row system with zero w-part; same instances
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, proof of Theorem 4, Statement (ii.), pp.13–14

import Mathlib
import Definitions.Def_NashStackelberg_IsPNE
import Definitions.Def_NashStackelberg_IsMNE
import Definitions.Def_NashStackelberg_NASP_Ftilde
import Definitions.Def_NashStackelberg_NASP_cost

open MeasureTheory

namespace NashStackelberg

/-- **The means of an MNE of `N` form a PNE of `Ñ`** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, proof of Theorem 4, Statement
(ii.), pp.13–14: "we show that if N has an MNE, then Step 4 obtains a PNE for Ñ").

Let `σ` be an MNE of the NASP `N` in which every mixed strategy `σⁱ` has a finite first moment.
Then the profile of means `x̃ⁱ = ∫ x dσⁱ` is a PNE of the convexified game `Ñ`: each `x̃ⁱ` lies in
`cl conv(𝓕ⁱ)` and no player can lower its cost by deviating within `cl conv(𝓕ⁱ)`.

**Formalization Note.** The page's MNE has finite support `(x̂ⁱ, pⁱ)` and `x̃ⁱ = Σⱼ pⁱⱼ x̂ⁱⱼ`
(p.11 restricts attention to finite-support MNEs); here every MNE whose strategies have a finite
first moment is covered, finite supports included. -/
theorem statement_ii {n : ℕ} (N : NASP n) (σ : (i : Fin n) → Measure (N.Var i → ℝ))
    (hσ : IsMNE N.F N.cost σ) (hint : ∀ i, Integrable id (σ i)) :
    IsPNE N.Ftilde N.cost (fun i => ∫ y, y ∂(σ i)) := by sorry

end NashStackelberg
