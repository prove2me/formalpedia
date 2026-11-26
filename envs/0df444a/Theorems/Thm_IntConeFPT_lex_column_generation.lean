-- Prove2me | Theorems.Thm_IntConeFPT_lex_column_generation
-- name    : IntConeFPT.lex_column_generation
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:41:26.779639+00:00
-- url     : https://prove2.me/theorems/df2d57b7-2585-4658-9517-04c14f65ea22
-- title:
--   Lexicographic LP by column generation: GLS strong optimization from a pricing oracle, with primal recovery and perturbation
-- statement:
--   Let $T\subseteq\mathbb Z^d\times\mathbb R^k$ be a set of generators (possibly infinite), let $A\subseteq T$, and let $c,s:\mathbb R^d\to\mathbb R$ be a primary and a secondary cost depending on the integer coordinates. Consider the linear program
--   $$
--   \Phi(z,w,n)=\min\Bigl\{\sum_g\theta_g\,c(x_g)\ :\ \theta\ge0\ \text{finitely supported on }T,\ \sum_g\theta_g\,(x_g,u_g)=(z,w),\ \sum_g\theta_g=n\Bigr\}
--   $$
--   and its dual $\max\{\langle a,(z,w)\rangle+bn : \langle a,(x,u)\rangle+b\le c(x)\ \forall (x,u)\in T\}$.
--
--   Fix exponents $e,K$. There are a constant $C$ and, **for every machine $P$**, a machine $W$ with the following property. Let $\mathrm{ctx}$ be any word and $B\ge1$, and suppose that $P$ is a **pricing oracle**: on input $(\mathrm{ctx},\varepsilon,a)$ with rational $\varepsilon\ge0$ and $a\in\mathbb Q^{d+k}$, it returns within $B\cdot\ell^{e}$ steps ($\ell$ the query length) a rational generator $(x,u)\in A$ together with $c(x)$ and $s(x)$, of encoding length at most $|\mathrm{ctx}|^K$, minimizing $c+\varepsilon s-\langle a,\cdot\rangle$ over all of $T$. Then for every rational $(z,w,n)$ in the homogenized hull ($n=0$ and $(z,w)=0$, or $n>0$ and $(z,w)/n\in\operatorname{conv}T$), the machine $W$, on input $(d,k,z,w,n,\mathrm{ctx})$, outputs within $B\cdot L^{C}$ steps ($L$ the input length), with output length at most $L^C$:
--
--   1. the optimal value $\varphi=\Phi(z,w,n)$, which is a lower bound for every representation on $T$;
--   2. a dual pair $(a^\star,b^\star)$, feasible for all of $T$, with $\varphi=\langle a^\star,(z,w)\rangle+b^\star n$;
--   3. an optimal representation by at most $d+k+1$ pairwise distinct generators of $A$ with positive rational multiplicities, which is lexicographically optimal: among all representations on $T$ of primary cost at most $\varphi$ it minimizes $\sum_g\theta_g s(x_g)$.
--
--   The output is prefixed by $d$ and $k$.
--
--   This is the linear-programming engine of the proof of Lemma 5. The dual is solved by the ellipsoid method, with the pricing oracle as strong separation oracle for the dual feasible region [GLS88, Theorem 6.4.9]. An optimal basic primal solution is recovered on the separating columns [GLS88, Lemma 6.5.15]. A second run with the cost $c+\varepsilon s$ for a sufficiently small rational $\varepsilon$, computed from the encoding bounds, makes it lexicographically optimal. The encoding bound $|\mathrm{ctx}|^K$ on the oracle's answers gives the facet-complexity bound for the dual polyhedron that GLS requires.
--
--   **Formalization Note.** Machines are the mission's `Machine`/`RunsWithin`. The oracle is a machine $P$ (quantified before $W$) rather than an oracle tape, so the theorem is a composition statement: $W$ simulates $P$ on the queries it generates. The time bound $B\cdot\ell^e$ of the oracle is inherited multiplicatively, which covers bounds of the form $2^{O(d^2\log(d+1))}\ell^{O(1)}$. Columns are $\mathbb Z^d\times\mathbb Q^k$; taking $d=0$ gives arbitrary rational columns.
-- source:
--   Grötschel–Lovász–Schrijver, Geometric Algorithms and Combinatorial Optimization (Springer 1988), Theorem 6.4.9 and Lemma 6.5.15, as applied in Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, pp.35–36 (dual (3.1b) solved via the separation oracle (B.1); lexicographic perturbation f̃ = f + εp)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

theorem lex_column_generation :
    ∀ e K : ℕ, ∃ C : ℕ, ∀ P : Machine, ∃ W : Machine,
      ∀ (d k : ℕ) (ctx : List Sym) (T A : Set (Gen d k)) (c s : (Fin d → ℝ) → ℝ) (B : ℝ),
        1 ≤ B → A ⊆ T →
        (∀ (ε : ℚ), 0 ≤ ε → ∀ (ax : Fin d → ℚ) (au : Fin k → ℚ),
          ∃ (x : Fin d → ℤ) (u : Fin k → ℚ) (cq sq : ℚ),
            ratGen x u ∈ A ∧ (cq : ℝ) = c (fun i => (x i : ℝ)) ∧
            (sq : ℝ) = s (fun i => (x i : ℝ)) ∧
            (∀ g ∈ T, (cq : ℝ) + (ε : ℝ) * sq - pairing (ratPair ax au) (ratGen x u).toReal ≤
              c (fun i => (g.1 i : ℝ)) + (ε : ℝ) * s (fun i => (g.1 i : ℝ)) -
                pairing (ratPair ax au) g.toReal) ∧
            (encGen x u ++ encRat cq ++ encRat sq ++ [3]).length ≤ ctx.length ^ K ∧
            RunsWithin P (ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au)
              (encGen x u ++ encRat cq ++ encRat sq ++ [3])
              (B * ((ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au).length : ℝ) ^ e)) →
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
            RunsWithin W inp (encNat d ++ [3] ++ encNat k ++ [3] ++ encOracle o)
              (B * (inp.length : ℝ) ^ C) := by sorry

end IntConeFPT
