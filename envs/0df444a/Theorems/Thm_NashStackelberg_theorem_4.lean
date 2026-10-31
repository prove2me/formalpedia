-- Prove2me | Theorems.Thm_NashStackelberg_theorem_4
-- name    : NashStackelberg.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:58.607993+00:00
-- url     : https://prove2.me/theorems/806f9dda-9aad-4232-8655-23f5cdadb56c
-- title:
--   Theorem 4, p.12 — Algorithm 1 returns an MNE or correctly answers no (corrected: totality needs conv 𝓕ⁱ closed)
-- statement:
--   Let $N=(S^1,\dots,S^n)$ be a NASP, with any number of players, followers and variables, and let $\widetilde N$ be its convexified game, in which player $i$ minimizes the same cost over $\mathrm{cl\,conv}(\mathcal F^i)$. Write $|\mathcal C^i|$ for the number of complementarity conditions describing player $i$'s followers. Then:
--
--   1. **(a) Finiteness.** For every player $i$, $\mathcal F^i$ is the union of $2^{|\mathcal C^i|}$ polyhedra $\{x : A_\theta x\le b_\theta\}$, one for each $\theta\in\{0,1\}^{|\mathcal C^i|}$, and $\mathrm{cl\,conv}(\mathcal F^i)$ is the projection of a polyhedron,
--   $$
--   \mathrm{cl\,conv}(\mathcal F^i)=\{x:\ \exists u,\ Ax+Bu\le b\}.
--   $$
--   So $\widetilde N$ is a facile game and Step 4 of Algorithm 1 is a linear complementarity problem.
--   2. **(b) Output (i) is an MNE.** Whenever Algorithm 1 returns lotteries $(\hat x^i,p^i)$, the profile in which each player $i$ plays $\hat x^i_j$ with probability $p^i_j$ is a mixed Nash equilibrium of $N$.
--   3. **(c) Output (ii) is correct.** Whenever Algorithm 1 returns `no`, $N$ has no mixed Nash equilibrium (with mixed strategies of finite first moment).
--   4. **(d) Totality, corrected.** If $\mathrm{conv}(\mathcal F^i)$ is closed for every player $i$, then Algorithm 1 returns an output, and every returned lottery has at most $2^{|\mathcal C^i|}$ points.
--
--   Theorem 4 makes the computation of mixed equilibria of NASPs, a $\Sigma_2^p$-hard problem, reducible to one LCP over a convexified game: a pure equilibrium of $\widetilde N$ is the mean profile of a mixed equilibrium of $N$, and the absence of one certifies that $N$ has no mixed equilibrium.
--
--   **Formalization Note** Algorithm 1 is represented by the relation between a NASP and its possible outputs (`Alg1Output`): `no` exactly when $\widetilde N$ has no PNE, and lotteries built from a PNE $\tilde x$ of $\widetilde N$ by Step 6 (a point mass at $\tilde x^i$ when $\tilde x^i\in\mathcal F^i$) or Step 7 (a convex combination of points of $\mathcal F^i$ with mean $\tilde x^i$). Clauses (b) and (c) need no hypothesis; only (d) uses closedness of $\mathrm{conv}(\mathcal F^i)$.
--
--   Differences from the source:
--   - correction: Algorithm 1 always returns either (i) an MNE or (ii) no → it returns an output when conv(𝓕ⁱ) is closed for every i (clause (d)); (b) and (c) hold unconditionally; reason: Step 7 cannot decompose a PNE point of Ñ in cl conv(𝓕ⁱ) ∖ conv(𝓕ⁱ). Two-player NASP: player 1 has leader (a, b) and followers y_b (min y_b s.t. y_b ≥ −b, y_b ≥ b − 1) and z (min z − bz s.t. z ≥ 0), 𝓢¹ = {y_b ≥ 0, 0 ≤ b ≤ 1, 0 ≤ a ≤ z}, cost b + y·a; player 2 has leader y ∈ [−1, 1], follower v (min v s.t. v ≥ 0), cost (1 − a)·y. Then 𝓕¹ = {0} ∪ {(a, 1, 0, z) : 0 ≤ a ≤ z}, every PNE of Ñ has (a, b) = (1, 0) ∉ conv(𝓕¹), and N has no MNE
--   - reading: Algorithm 1 terminates in a finite number of steps (kⁱ ≤ 2^{𝓒ⁱ}, Step 4 is an LCP) → clause (a): 𝓕ⁱ is the union of 2^{|𝓒ⁱ|} polyhedra and cl conv(𝓕ⁱ) is the projection of a polyhedron; reason: with an LCP oracle the loops are trivially finite; (a) is the content the proof gives
--   - reading: Algorithm 1 as a procedure with choices in Steps 4 and 7 → the relation Alg1Output between N and its possible outputs; reason: a statement about every possible output is a statement about every run
--   - generalization: (ii) no if N has no MNE, with MNEs restricted to finite support (p.11) → no ⇒ N has no MNE whose mixed strategies have finite first moments; reason: every finite-support MNE is one
--   - generalization: Theorem 4 does not bound the support of the returned lotteries → (d) also bounds each returned lottery by 2^{|𝓒ⁱ|} points; reason: an additional conclusion; p.11 says the players randomize over at most kⁱ ≤ 2^{|𝓒ⁱ|} pure strategies
--   - reading: |𝓒ⁱ| = the number of complementarity conditions 0 ≤ xⁱⱼ ⊥ zⁱⱼ ≥ 0 describing SOL(P(wⁱ)), with Mⁱ, qⁱ of (3) unspecified → the number of constraint rows of player i's followers (one KKT multiplier per row); reason: the followers' problems are convex QPs with linear constraints, whose KKT system has exactly one complementarity condition per row
--   - generalization: one leader dimension nℓ and one follower dimension nf for all players (xⁱ ∈ ℝ^{nℓ+nf}) → each player has its own numbers of leader variables, followers and follower variables; reason: the statement specializes to equal dimensions
--   - generalization: Qₖ a positive semi-definite matrix → vᵀQₖv ≥ 0 for all v, Qₖ not required to be symmetric; reason: covers every symmetric PSD matrix; only the quadratic form enters the followers' objectives
--   - encoding: follower constraints y ∈ 𝓕 (𝓕 a polyhedron) and Ax + By ≤ b → one row system Aₖw + Bₖyₖ ≤ bₖ per follower; reason: a polyhedron 𝓕 is a row system with zero w-part; same instances
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Theorem 4, p.12, and its proof, pp.12–14

import Mathlib
import Definitions.Def_NashStackelberg_IsPNE
import Definitions.Def_NashStackelberg_IsMNE
import Definitions.Def_NashStackelberg_NASP_F
import Definitions.Def_NashStackelberg_NASP_rows
import Definitions.Def_NashStackelberg_NASP_Ftilde
import Definitions.Def_NashStackelberg_NASP_cost
import Definitions.Def_NashStackelberg_Lottery_measure
import Definitions.Def_NashStackelberg_Alg1Output

open MeasureTheory Matrix

namespace NashStackelberg

/-- **Theorem 4: the Enumeration Algorithm returns an MNE or correctly answers `no`** (Carvalho,
Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6,
Theorem 4, p.12, with its proof, pp.12–14: "Algorithm 1 terminates in a finite number of steps and
returns either (i) an MNE for N so that each player i plays the strategy x̂ⁱⱼ with probability pⁱⱼ,
or (ii) no if N has no MNE").

For every NASP `N` (any number of players, followers and variables):

* **(a) finiteness** — for every player `i`, `𝓕ⁱ` is the union of `2^{|𝓒ⁱ|}` polyhedra (one per
  `θ ∈ {0,1}^{|𝓒ⁱ|}`), and `cl conv(𝓕ⁱ)` is the projection of a polyhedron, so `Ñ` is a facile game
  and Step 4 is an LCP ("kⁱ ≤ 2^{𝓒ⁱ} for any i, and Step 4 is an LCP");
* **(b) output (i)** — every lottery profile Algorithm 1 can return is an MNE of `N`;
* **(c) output (ii)** — if Algorithm 1 can return `no`, then `N` has no MNE (with mixed strategies
  of finite first moment);
* **(d) totality (corrected)** — if `conv(𝓕ⁱ)` is closed for every player `i`, Algorithm 1 returns
  some output, and the lottery of each player has at most `2^{|𝓒ⁱ|}` points.

**Formalization Note.** Correction: without the closedness hypothesis (d) is false (Step 7 cannot
decompose a PNE point of `Ñ` in `cl conv(𝓕ⁱ) \ conv(𝓕ⁱ)`; a two-player NASP in which every PNE of
`Ñ` is such a point and `N` has no MNE is in the mission notes). (b) and (c) need no hypothesis.
"Terminates in a finite number of steps" is read as (a). `|𝓒ⁱ|` is `N.rows i`. -/
theorem theorem_4 {n : ℕ} (N : NASP n) :
    (∀ i, (∃ (m : (Fin (N.rows i) → Bool) → ℕ)
        (A : (θ : Fin (N.rows i) → Bool) → Matrix (Fin (m θ)) (N.Var i) ℝ)
        (b : (θ : Fin (N.rows i) → Bool) → Fin (m θ) → ℝ),
        N.F i = ⋃ θ, {x | A θ *ᵥ x ≤ b θ}) ∧
      (∃ (p r : ℕ) (A : Matrix (Fin r) (N.Var i) ℝ) (B : Matrix (Fin r) (Fin p) ℝ)
        (b : Fin r → ℝ), N.Ftilde i = {x | ∃ u, A *ᵥ x + B *ᵥ u ≤ b})) ∧
    (∀ L, Alg1Output N (some L) → IsMNE N.F N.cost (fun i => (L i).measure)) ∧
    (Alg1Output N none → ¬ ∃ σ : (i : Fin n) → Measure (N.Var i → ℝ),
      IsMNE N.F N.cost σ ∧ ∀ i, Integrable id (σ i)) ∧
    ((∀ i, IsClosed (convexHull ℝ (N.F i))) →
      ∃ out, Alg1Output N out ∧ ∀ L, out = some L → ∀ i, (L i).k ≤ 2 ^ N.rows i) := by sorry

end NashStackelberg
