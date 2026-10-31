-- Prove2me | Theorems.Thm_NashStackelberg_feasible_region_union_polyhedra
-- name    : NashStackelberg.feasible_region_union_polyhedra
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:42.890931+00:00
-- url     : https://prove2.me/theorems/ffafcef6-1de9-45f2-bc24-d294236ef1f3
-- title:
--   Eq. (3) and Definition 6, pp.10–11 — $\mathcal F^i$ is the union of $2^{|\mathcal C^i|}$ complementarity polyhedra
-- statement:
--   Let $N$ be a NASP and $i$ a player, and let $|\mathcal C^i|$ be the number of complementarity conditions describing the followers' solution set $\mathrm{SOL}(P^i(w^i))$, one for each constraint row of player $i$'s followers. Then there are polyhedra
--   $$
--   K_\theta=\{x: A_\theta x\le b_\theta\},\qquad \theta\in\{0,1\}^{|\mathcal C^i|},
--   $$
--   one for each binary vector $\theta$ (some possibly empty), such that
--   $$
--   \mathcal F^i=\bigcup_{\theta\in\{0,1\}^{|\mathcal C^i|}} K_\theta .
--   $$
--
--   The vector $\theta$ records, for every complementarity condition $0\le\lambda_j\perp s_j\ge0$, which side is forced to zero; the corresponding polyhedron is the complementarity polyhedron $\mathcal P^i(\theta)$ of Definition 6, seen in the space of $x^i$. This is the structural fact behind Algorithm 1: the non-convex feasible region of a Stackelberg player is a finite union of polyhedra, so the closure of its convex hull can be computed by Balas's theorem, and the number of pieces bounds both the work of Step 2 and the support of the lotteries returned.
--
--   **Formalization Note** Polyhedra are written $\{x : A x\le b\}$ componentwise; the union is indexed by functions $\theta:\{1,\dots,|\mathcal C^i|\}\to\{0,1\}$.
--
--   Differences from the source:
--   - reading: |𝓒ⁱ| = the number of complementarity conditions 0 ≤ xⁱⱼ ⊥ zⁱⱼ ≥ 0 describing SOL(P(wⁱ)), with Mⁱ, qⁱ of (3) unspecified → the number of constraint rows of player i's followers (one KKT multiplier per row); reason: the followers' problems are convex QPs with linear constraints, whose KKT system has exactly one complementarity condition per row
--   - reading: 𝓕ⁱ = ⋃_θ 𝓟ⁱ(θ) with 𝓟ⁱ(θ) ⊆ 𝓞ⁱ, a set of pairs (xⁱ, zⁱ) → 𝓕ⁱ is the union of polyhedra in xⁱ-space indexed by θ ∈ {0,1}^{|𝓒ⁱ|}; reason: the page's union equates a set of xⁱ with sets of (xⁱ, zⁱ); zⁱ = Mⁱxⁱ + qⁱ is determined by xⁱ and the multipliers, and projections of polyhedra are polyhedra
--   - generalization: one leader dimension nℓ and one follower dimension nf for all players (xⁱ ∈ ℝ^{nℓ+nf}) → each player has its own numbers of leader variables, followers and follower variables; reason: the statement specializes to equal dimensions
--   - generalization: Qₖ a positive semi-definite matrix → vᵀQₖv ≥ 0 for all v, Qₖ not required to be symmetric; reason: covers every symmetric PSD matrix; only the quadratic form enters the followers' objectives
--   - encoding: follower constraints y ∈ 𝓕 (𝓕 a polyhedron) and Ax + By ≤ b → one row system Aₖw + Bₖyₖ ≤ bₖ per follower; reason: a polyhedron 𝓕 is a row system with zero w-part; same instances
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, eq. (3), p.10; Definition 6 and the sentence after it, p.11

import Mathlib
import Definitions.Def_NashStackelberg_NASP_F
import Definitions.Def_NashStackelberg_NASP_rows

open Matrix

namespace NashStackelberg

/-- **The player feasible region is the union of the complementarity polyhedra** (Carvalho,
Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6,
eq. (3), p.10, Definition 6 and the sentence after it, p.11:
"𝓕ⁱ is the finite union of all the complementarity polyhedra, i.e., 𝓕ⁱ = ⋃_{θⁱ∈{0,1}^{|𝓒ⁱ|}} 𝓟ⁱ(θⁱ)").

For every NASP `N` and player `i` there are polyhedra `Kθ = {x : A_θ x ≤ b_θ}`, one for each
binary vector `θ ∈ {0,1}^{|𝓒ⁱ|}`, whose union is `𝓕ⁱ`.

**Formalization Note.** `|𝓒ⁱ|` is `N.rows i`, the number of constraint rows of player `i`'s
followers (one complementarity condition each). The page's polyhedra `𝓟ⁱ(θ)` live in the space of
`(xⁱ, zⁱ)` of (3); the union is stated for their projections to `xⁱ`-space, which are polyhedra.
Polyhedra are written `{x | A *ᵥ x ≤ b}` (componentwise), possibly empty. -/
theorem feasible_region_union_polyhedra {n : ℕ} (N : NASP n) (i : Fin n) :
    ∃ (m : (Fin (N.rows i) → Bool) → ℕ)
      (A : (θ : Fin (N.rows i) → Bool) → Matrix (Fin (m θ)) (N.Var i) ℝ)
      (b : (θ : Fin (N.rows i) → Bool) → Fin (m θ) → ℝ),
      N.F i = ⋃ θ, {x | A θ *ᵥ x ≤ b θ} := by sorry

end NashStackelberg
