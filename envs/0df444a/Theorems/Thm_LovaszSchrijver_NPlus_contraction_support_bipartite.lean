-- Prove2me | Theorems.Thm_LovaszSchrijver_NPlus_contraction_support_bipartite
-- name    : LovaszSchrijver.NPlus.contraction_support_bipartite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:01:25.229304+00:00
-- url     : https://prove2.me/theorems/3920041c-d220-45c2-a4bd-422d73abd27f
-- title:
--   Section 2.d — contracting a positive node of a clique, odd hole, odd wheel or odd antihole constraint leaves a bipartite positive support
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes. For a coefficient vector $a \in \mathbb R^V$ and a node $v$, the contraction of $v$ is the vector $a'$ with $a'_w = 0$ for $w = v$ or $w$ adjacent to $v$, and $a'_w = a_w$ otherwise. The paper states (p. 183): "The clique, odd hole, odd wheel, and odd antihole constraints have the property that, contracting any node with a positive coefficient, we get an inequality in which the nodes with positive coefficients induce a bipartite subgraph."
--
--   Formally, in each of the following four cases, for every node $v$ with $a_v > 0$, the subgraph of $G$ induced by $\{w : a'_w > 0\}$ is 2-colourable:
--
--   1. $a = \chi^B$ for a clique $B$ with $|B| \ge 3$;
--   2. $a = \chi^C$ for an odd hole $C$;
--   3. $a$ the wheel coefficient vector of an odd wheel $U$ with center $u_0$ (1 on the rim, $(|U|-2)/2$ at $u_0$);
--   4. $a = \chi^D$ for an odd antihole $D$ (with $|D| \ge 5$).
--
--   Together with Lemma 2.14 and the bipartite-support remark this gives Corollary 2.15.
--
--   **Formalization Note** The condition $|B| \ge 3$ on cliques matches the main theorem (Corollary 2.15), where it is needed; the statement here holds without it.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 183, Section 2.d

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_Constraints

namespace LovaszSchrijver.NPlus

theorem contraction_support_bipartite {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card → ∀ v, 0 < chi B v →
        (G.induce {w | 0 < contractCoeff G (chi B) v w}).Colorable 2) ∧
    (∀ C : Finset V, IsOddHole G C → ∀ v, 0 < chi C v →
        (G.induce {w | 0 < contractCoeff G (chi C) v w}).Colorable 2) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ → ∀ v, 0 < wheelCoeff U u₀ v →
        (G.induce {w | 0 < contractCoeff G (wheelCoeff U u₀) v w}).Colorable 2) ∧
    (∀ D : Finset V, IsOddAntihole G D → ∀ v, 0 < chi D v →
        (G.induce {w | 0 < contractCoeff G (chi D) v w}).Colorable 2) := by sorry

end LovaszSchrijver.NPlus
