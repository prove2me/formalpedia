-- Prove2me | Theorems.Thm_NashStackelberg_eq_4a
-- name    : NashStackelberg.eq_4a
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:05.442476+00:00
-- url     : https://prove2.me/theorems/ff0306ac-434b-44c1-920f-82a286509924
-- title:
--   (4a), p.13 — the expected cost of independent mixed strategies is the cost of their means
-- statement:
--   Let $N$ be a NASP. Suppose every player $j$ plays a mixed strategy $\sigma^j$, a probability distribution on its joint vectors with finite first moment, independently of the others, and let $\tilde x^j=\mathbb E_{X^j\sim\sigma^j}[X^j]$ be its mean. Then for every player $i$:
--
--   1. the expected cost equals the cost at the profile of means,
--   $$
--   \mathbb E_{X\sim\sigma}\Big[\big(c^i+C^iX^{-i}\big)^{\!\top}X^i\Big]=\big(c^i+C^i\tilde x^{-i}\big)^{\!\top}\tilde x^i ;
--   $$
--   2. for every fixed $x'$, $\ \mathbb E_{X\sim\sigma}\big[(c^i+C^iX^{-i})^\top x'\big]=(c^i+C^i\tilde x^{-i})^\top x'$.
--
--   Because each cost is linear in the player's own vector and the players randomize independently, a profile of mixed strategies is payoff-equivalent to the profile of its means. This identity drives both directions of the correspondence between mixed equilibria of $N$ and pure equilibria of $\widetilde N$.
--
--   Differences from the source:
--   - generalization: finite lotteries (x̂ⁱⱼ, pⁱⱼ) → any independent mixed strategies with finite first moment; reason: a finite lottery is such a mixed strategy
--   - generalization: the identity for the expected cost of the profile → also the identity for every fixed deviation x′ of player i (clause 2); reason: an additional conclusion, used in the proofs of Statements (i.) and (ii.)
--   - generalization: one leader dimension nℓ and one follower dimension nf for all players (xⁱ ∈ ℝ^{nℓ+nf}) → each player has its own numbers of leader variables, followers and follower variables; reason: the statement specializes to equal dimensions
--   - generalization: Qₖ a positive semi-definite matrix → vᵀQₖv ≥ 0 for all v, Qₖ not required to be symmetric; reason: covers every symmetric PSD matrix; only the quadratic form enters the followers' objectives
--   - encoding: follower constraints y ∈ 𝓕 (𝓕 a polyhedron) and Ax + By ≤ b → one row system Aₖw + Bₖyₖ ≤ bₖ per follower; reason: a polyhedron 𝓕 is a row system with zero w-part; same instances
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, proof of Theorem 4, Statement (i.), (4a), p.13

import Mathlib
import Definitions.Def_NashStackelberg_NASP_cost

open MeasureTheory

namespace NashStackelberg

/-- **Expected cost of independent mixed strategies is the cost of their means** (Carvalho,
Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6,
proof of Theorem 4, Statement (i.), (4a), p.13:
`E_{X̂∼p}[(cⁱ + CⁱX̂⁻ⁱ)ᵀ X̂ⁱ] = Σ_{j'} Σ_j p⁻ⁱ_{j'} pⁱⱼ (cⁱ + Cⁱx̂⁻ⁱ_{j'})ᵀ x̂ⁱⱼ = (cⁱ + Cⁱx̃⁻ⁱ)ᵀ x̃ⁱ`).

Let `N` be a NASP and let every player `j` play a mixed strategy `σʲ`, a probability measure on
its joint vectors with finite first moment and mean `x̃ʲ = ∫ x dσʲ`, independently of the others.
Then for every player `i`:

1. the expected cost of `i` equals its cost at the profile of means,
   `E_{X∼σ}[fⁱ(X)] = fⁱ(x̃)`;
2. for every fixed `x'`, `E_{X∼σ}[fⁱ(x', X⁻ⁱ)] = fⁱ(x', x̃⁻ⁱ)`.

**Formalization Note.** The page states (4a) for finite lotteries; the statement here holds for
all integrable mixed strategies (a finite lottery is one) and adds the deviation form 2., which
the proofs of Statements (i.) and (ii.) use. Independence is the product measure `Measure.pi σ`. -/
theorem eq_4a {n : ℕ} (N : NASP n) (σ : (i : Fin n) → Measure (N.Var i → ℝ))
    [∀ i, IsProbabilityMeasure (σ i)] (hσ : ∀ i, Integrable id (σ i)) (i : Fin n) :
    ∫ x, N.cost i x ∂(Measure.pi σ) = N.cost i (fun j => ∫ y, y ∂(σ j)) ∧
      ∀ x' : N.Var i → ℝ,
        ∫ x, N.cost i (Function.update x i x') ∂(Measure.pi σ) =
          N.cost i (Function.update (fun j => ∫ y, y ∂(σ j)) i x') := by sorry

end NashStackelberg
