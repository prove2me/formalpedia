-- Prove2me | Theorems.Thm_NearLinIsing_proposition_4_1
-- name    : NearLinIsing.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:18.643598+00:00
-- url     : https://prove2.me/theorems/e8836e75-28ed-438a-bb5f-9e80b2fe6d8d
-- title:
--   Proposition 4.1 — reduction to maximum degree three
-- statement:
--   Let $G$ be a simple graph with $m$ edges and maximum degree at most $\Delta\ge3$, and let $r>0$ satisfy $(\Delta-1)r\le1$. The port graph $H$ of $G$ satisfies:
--
--   1. every port has degree at most three, and $|E(H)|\le3m$;
--   2. every weight $t_e$ is $r$ or $1$;
--   3. restriction to original edges is a bijection from the even subgraphs of $H$ onto those of $G$, and $\prod_{e\in F}t_e=r^{|F\cap E(G)|}$ for every even $F$;
--   4. every complex eigenvalue of the nonbacktracking matrix has modulus at most one, that is, $\rho(B_t)\le1$;
--   5. the explicit vector $z$ is positive and $Kz\le z$;
--   6. the transition probabilities (13) are nonnegative and every row sums to at most one.
--
--   This reduction makes even subgraphs vertex-disjoint unions of cycles, and the normalization (13) drives the exploration.
--
--   Differences from the source:
--   - encoding: there is a graph H with these properties → the statement is about the concrete port graph `portGraph G r`; reason: it is the construction of p. 18, and it implies the existential
--   - encoding: a graph G with maximum degree at most Δ → a well-formed `IncGraph` with `MaxDegLe Δ`; reason: the input format of §2.6
--   - encoding: ρ(B_t) ≤ 1 → every element of the complex spectrum of B_t has norm at most 1; reason: this is the definition of the spectral radius of a finite matrix
--   - encoding: z gives the transition probabilities in (13) → nonnegativity of P_H and row sums at most 1 are stated; reason: this is what the exploration on p. 19 uses of (13)
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Proposition 4.1, p. 18; construction p. 18; proof pp. 18–19

import Mathlib
import Definitions.Def_NearLinIsing_buildPort

namespace NearLinIsing

/-- **Proposition 4.1** (Reduction to maximum degree three), p. 18.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Proposition 4.1, p. 18; construction ("The degree reduction"), p. 18;
proof, pp. 18–19.

Let `G` be well formed with maximum degree at most `Δ ≥ 3`, and let `r > 0` with `(Δ − 1) r ≤ 1`.
The port graph `H = portGraph G r` (2-core, each core vertex of degree `d` replaced by a path of `d`
ports, original edges of weight `r`, path edges of weight `1`) satisfies:
1. every port has degree at most three;
2. `|E(H)| ≤ 3m`;
3. every weight is `r` or `1`;
4. restriction to original edges is a bijection from the even subgraphs of `H` onto those of `G`;
5. it preserves weights: `∏_{e ∈ F} t_e = r^{|restrict F|}` for every even `F`;
6. `ρ(B_t) ≤ 1`: every complex eigenvalue of the nonbacktracking matrix has modulus at most `1`;
7. the explicit vector `z` of p. 18 is positive and `K z ≤ z`, where `K` keeps the transitions of
   `B_t` within strongly connected components;
8. the transition probabilities (13), `P_H(a,b) = K_{ab} z_b / z_a`, are nonnegative and every row
   sums to at most `1`.

**Formalization Note.** The paper's "there is a graph H" is stated for the paper's construction
(stronger). `ρ(B_t) ≤ 1` is stated through the spectrum of `B_t` as a complex matrix. -/
theorem proposition_4_1 (Δ : ℕ) (hΔ : 3 ≤ Δ) (G : IncGraph) (hG : G.WellFormed)
    (hdeg : G.MaxDegLe Δ) (r : ℝ) (hr : 0 < r) (hΔr : ((Δ : ℝ) - 1) * r ≤ 1) :
    (∀ p : ℕ, (portGraph G r).deg p ≤ 3) ∧
    (portGraph G r).ne ≤ 3 * G.m ∧
    (∀ e : Fin (portGraph G r).ne, (portGraph G r).t e = r ∨ (portGraph G r).t e = 1) ∧
    Set.BijOn ((portGraph G r).restrict G) {F | (portGraph G r).IsEven F} {F | G.IsEven F} ∧
    (∀ F : Finset (Fin (portGraph G r).ne), (portGraph G r).IsEven F →
      ∏ e ∈ F, (portGraph G r).t e = r ^ ((portGraph G r).restrict G F).card) ∧
    (∀ μ ∈ spectrum ℂ ((portGraph G r).Bt.map (algebraMap ℝ ℂ)), ‖μ‖ ≤ 1) ∧
    (∀ a, 0 < (portGraph G r).zMath r a) ∧
    (∀ a, ∑ b, (portGraph G r).Kmat a b * (portGraph G r).zMath r b ≤ (portGraph G r).zMath r a) ∧
    (∀ a b, 0 ≤ (portGraph G r).PHmath r a b) ∧
    (∀ a, ∑ b, (portGraph G r).PHmath r a b ≤ 1) := by sorry

end NearLinIsing
