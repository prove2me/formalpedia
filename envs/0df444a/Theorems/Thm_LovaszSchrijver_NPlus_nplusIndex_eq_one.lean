-- Prove2me | Theorems.Thm_LovaszSchrijver_NPlus_nplusIndex_eq_one
-- name    : LovaszSchrijver.NPlus.nplusIndex_eq_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:01:58.7375+00:00
-- url     : https://prove2.me/theorems/bd5f172d-78bd-4cc2-861a-12249b0cefe2
-- title:
--   Corollary 2.15 — clique, odd hole, odd wheel and odd antihole constraints have N₊-index 1
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes. For a valid inequality $a^{\mathsf T}x \le b$ of $\mathrm{STAB}(G)$, its $N_+$-index is the least $r \ge 0$ such that the inequality holds on $N_+^r(G)$, the $r$-th iterate of the Lovász–Schrijver semidefinite operator applied to $\mathrm{FR}(G)$ and dehomogenized; $N_+^0(G) = \mathrm{FRAC}(G)$.
--
--   Corollary 2.15 (p. 183): clique, odd hole, odd wheel and odd antihole constraints have $N_+$-index exactly 1. That is:
--
--   1. for every clique $B$ of $G$ with $|B| \ge 3$, $\sum_{i\in B} x_i \le 1$ has $N_+$-index 1;
--   2. for every odd hole $C$ (chordless odd cycle, triangles included), $\sum_{i\in C} x_i \le \tfrac12(|C|-1)$ has $N_+$-index 1;
--   3. for every odd wheel $U$ with center $u_0$,
--   $$\sum_{i\in U\setminus\{u_0\}} x_i + \frac{|U|-2}{2}\,x_{u_0} \le \frac{|U|-2}{2}$$
--   has $N_+$-index 1;
--   4. for every odd antihole $D$ ($|D| \ge 5$), $\sum_{i\in D} x_i \le 2$ has $N_+$-index 1.
--
--   In each case the inequality holds on $N_+^1(G)$ and fails somewhere on $\mathrm{FRAC}(G)$. A consequence noted in the paper is that all $h$-perfect graphs, in particular all perfect and $t$-perfect graphs, satisfy $N_+(G) = \mathrm{STAB}(G)$: one round of the semidefinite operator already produces the stable set polytope.
--
--   **Formalization Note** Index 1 is stated exactly, as `IsLeast {t | valid on N₊ᵗ(G)} 1`. Cliques with at most two nodes are excluded ($|B| \ge 3$): their constraints $x_i \le 1$ and $x_i + x_j \le 1$ already hold on $\mathrm{FRAC}(G)$ and have index 0; the page introduces clique constraints as strengthening the edge constraints (2), which only cliques of size at least 3 do. See the definition files for the odd hole, odd antihole and odd wheel conventions.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 183, Corollary 2.15

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_Constraints

namespace LovaszSchrijver.NPlus

theorem nplusIndex_eq_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi B) 1} 1) ∧
    (∀ C : Finset V, IsOddHole G C →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi C) (((C.card : ℝ) - 1) / 2)} 1) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ →
        IsLeast {t : ℕ | Valid (NplusG t G) (wheelCoeff U u₀) (((U.card : ℝ) - 2) / 2)} 1) ∧
    (∀ D : Finset V, IsOddAntihole G D →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi D) 2} 1) := by sorry

end LovaszSchrijver.NPlus
