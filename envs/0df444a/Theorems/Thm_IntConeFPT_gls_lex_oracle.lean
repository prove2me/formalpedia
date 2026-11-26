-- Prove2me | Theorems.Thm_IntConeFPT_gls_lex_oracle
-- name    : IntConeFPT.gls_lex_oracle
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:51:19.681837+00:00
-- url     : https://prove2.me/theorems/ce4fe83c-f548-56e5-a2a7-af11c6130fe7
-- title:
--   GLS lexicographic column generation as an oracle algorithm — strong optimization, dual and basic primal from a pricing oracle
-- statement:
--   Let $T\subseteq\mathbb Z^d\times\mathbb R^k$ be a set of generators, $A\subseteq T$, and $c,s:\mathbb R^d\to\mathbb R$ a primary and a secondary cost. Consider the linear program
--   $$\min\Bigl\{\sum_g\theta_g c(x_g) : \theta\ge0 \text{ on } T,\ \sum_g\theta_g(x_g,u_g)=(z,w),\ \sum_g\theta_g=n\Bigr\}$$
--   and its dual $\max\{\langle a,(z,w)\rangle+bn:\ \langle a,(x,u)\rangle+b\le c(x)\ \forall(x,u)\in T\}$.
--
--   For every exponent $K$ there are a constant $C$ and one oracle machine $OM$ with the following property. Let $O$ be a **pricing oracle** for a context word $\mathrm{ctx}$: on the query $(\mathrm{ctx},\varepsilon,a)$ with rational $\varepsilon\ge0$ and $a\in\mathbb Q^{d+k}$, it answers a rational generator $(x,u)\in A$ minimizing $c+\varepsilon s-\langle a,\cdot\rangle$ over $T$, together with $c(x)$ and $s(x)$, the whole answer of length at most $|\mathrm{ctx}|^K$. Let $(z,w,n)$ be a rational point of the homogenized hull of $T$. Then, on input $(d,k,z,w,n,\mathrm{ctx})$ of length $L$, $OM$ halts within $L^C$ steps, each oracle call counting as one step. It asks only queries of this form of length at most $L^C$, and it outputs, with output length at most $L^C$,
--
--   1. the optimal value $\varphi$, a lower bound for the cost of every representation on $T$;
--   2. a dual pair, feasible on $T$, attaining $\varphi$;
--   3. an optimal representation by at most $d+k+1$ distinct generators of $A$ with positive multiplicities, which minimizes the secondary cost $\sum_g\theta_gs(x_g)$ among all representations on $T$ of primary cost at most $\varphi$.
--
--   This is the oracle-algorithmic content of the linear-programming step in the proof of Lemma 5. The dual feasible region is a polyhedron whose inequalities, the oracle's answers, have encoding length at most $|\mathrm{ctx}|^K$. The ellipsoid method with the pricing oracle as strong separation oracle solves the dual [GLS88, Thm 6.4.9]. An optimal basic primal solution is recovered from the separating columns [GLS88, Lemma 6.5.15]. A second run with the perturbed cost $c+\varepsilon s$, for $\varepsilon$ computed from the encoding bounds, makes the representation lexicographically optimal.
--
--   **Formalization Note.** The oracle model is `IntConeFPT_OracleMachine`: the oracle is an arbitrary function $O$ on words, specified only on the queries the machine may ask, and the permitted queries and their lengths are fixed by the predicate argument of `ORunsWithin`. The output is prefixed by $d$ and $k$. Columns are $\mathbb Z^d\times\mathbb Q^k$; $d=0$ gives arbitrary rational columns.
-- source:
--   Grötschel–Lovász–Schrijver, Geometric Algorithms and Combinatorial Optimization (Springer 1988), Theorem 6.4.9 and Lemma 6.5.15, as applied in Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, pp.35–36

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_OracleMachine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

theorem gls_lex_oracle :
    ∀ K : ℕ, ∃ C : ℕ, ∃ OM : OracleMachine,
      ∀ (d k : ℕ) (ctx : List Sym) (T A : Set (Gen d k)) (c s : (Fin d → ℝ) → ℝ),
        A ⊆ T → ∀ O : List Sym → List Sym,
        (∀ (ε : ℚ), 0 ≤ ε → ∀ (ax : Fin d → ℚ) (au : Fin k → ℚ),
          ∃ (x : Fin d → ℤ) (u : Fin k → ℚ) (cq sq : ℚ),
            ratGen x u ∈ A ∧ (cq : ℝ) = c (fun i => (x i : ℝ)) ∧
            (sq : ℝ) = s (fun i => (x i : ℝ)) ∧
            (∀ g ∈ T, (cq : ℝ) + (ε : ℝ) * sq - pairing (ratPair ax au) (ratGen x u).toReal ≤
              c (fun i => (g.1 i : ℝ)) + (ε : ℝ) * s (fun i => (g.1 i : ℝ)) -
                pairing (ratPair ax au) g.toReal) ∧
            (encGen x u ++ encRat cq ++ encRat sq ++ [3]).length ≤ ctx.length ^ K ∧
            O (ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au) =
              encGen x u ++ encRat cq ++ encRat sq ++ [3]) →
        ∀ (z : Fin d → ℚ) (w : Fin k → ℚ) (n : ℚ),
          ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) = 0 ∨
            (0 < (n : ℝ) ∧ ((n : ℝ)⁻¹ • (ratPair z w).1, (n : ℝ)⁻¹ • (ratPair z w).2) ∈
              convexHull ℝ (Gen.toReal '' T)) →
          let inp := encNat d ++ [3] ++ encNat k ++ [3] ++ encVec z ++ encVec w ++ encRat n ++ [3] ++ ctx
          ∃ o : ℚ × ((Fin d → ℚ) × (Fin k → ℚ)) × ℚ × List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ),
            (∀ θ : Gen d k →₀ ℝ, IsFracRep T θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
              (o.1 : ℝ) ≤ fracCost c θ) ∧
            (∀ g ∈ T, pairing (ratPair o.2.1.1 o.2.1.2) g.toReal + (o.2.2.1 : ℝ) ≤
              c (fun i => (g.1 i : ℝ))) ∧
            (o.1 : ℝ) = pairing (ratPair o.2.1.1 o.2.1.2) (ratPair z w) + (o.2.2.1 : ℝ) * n ∧
            o.2.2.2.length ≤ d + k + 1 ∧
            (o.2.2.2.map fun e => (e.1, e.2.1)).Nodup ∧
            (∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ A ∧ 0 < e.2.2) ∧
            (o.2.2.2.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
            (o.2.2.2.map fun e => (e.2.2 : ℝ)).sum = n ∧
            (o.2.2.2.map fun e => (e.2.2 : ℝ) * c (fun i => (e.1 i : ℝ))).sum = o.1 ∧
            (∀ θ : Gen d k →₀ ℝ, IsFracRep T θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
              fracCost c θ ≤ o.1 →
              (o.2.2.2.map fun e => (e.2.2 : ℝ) * s (fun i => (e.1 i : ℝ))).sum ≤ fracCost s θ) ∧
            (encOracle o).length ≤ inp.length ^ C ∧
            ORunsWithin OM O
              (fun q => q.length ≤ inp.length ^ C ∧ ∃ (ε : ℚ) (ax : Fin d → ℚ) (au : Fin k → ℚ),
                0 ≤ ε ∧ q = ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au)
              inp (encNat d ++ [3] ++ encNat k ++ [3] ++ encOracle o) (inp.length ^ C) := by sorry

end IntConeFPT
