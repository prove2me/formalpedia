-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_BoundedPattern_probability_union
-- name    : OAI.TorsionFreeZeroDivisors.BoundedPattern.probability_union
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:12:14.981377+00:00
-- url     : https://prove2.me/theorems/ba27a875-19fd-4878-b2df-205369df540c
-- title:
--   Proposition 3.1 (OpenAI), quantitative form — good bounded patterns are realized with probability $\le c\,(H+1)^{R+3I}e^{-L/(4800M)}$
-- statement:
--   Let $R,K,I,M>0$ and $T,H,B,Q,J$ be natural numbers, and let $n$ be a level at which the girth-conditioned sample space $\mathcal S(n)$ is nonempty and the readiness condition $\mathrm{Ready}(B,M,Q,J,n)$ holds. Then for every vertex $x$ of side $A$ and $y$ of side $B$,
--
--   $$\frac{\#\{r\in\mathcal S(n):\ \exists\,\mathfrak a\ \text{good, with}\ \mathfrak a\ \text{realized in}\ r\ \text{at}\ (x,y)\}}{\#\mathcal S(n)}\ \le\ c(R,K,T,I)\,(H+1)^{R+3I}\,\exp\!\Big(-\frac{L}{4800\,M}\Big),$$
--
--   where $L=L(\mathrm{size}(n))$ and $c(R,K,T,I)$ is an explicit natural number.
--
--   Here $\mathfrak a$ ranges over the bounded patterns with parameters $(R,K,T,I,H)$. Such a pattern is an abstract finite port graph with marked vertices and degree-two chains: at most $R$ chains and marked vertices, chain lengths at most $H$, at most $K$ paths, each a list of at most $T$ chains with one optional root path, and at most $I$ interval comparisons with endpoints in $[0,H]$. The pattern is good for $(B,Q,M,J,n)$ when every chain is traversed between $1$ and $M$ times, the paths are non-backtracking and closed except the root path, compared positions lie on distinct undirected edges, the total length lies in $[L,BL]$, at most a $1/2467200$ fraction of positions are unpaired, and two counting bounds involving $Q$ and $J$ hold. It is realized in $r$ when it embeds into the sampled graphs, with letters compatible with the comparisons and the root path starting at $x$ or $y$.
--
--   This is the union bound that proves Proposition 3.1. The proof of `OAI.TorsionFreeZeroDivisors.SampleGraph.exists_avoiding` checks readiness for all large $n$ and shows that the right-hand side tends to $0$.
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 7: “Proposition 3.1 (Bounded-pattern estimate). There is a constant $\varepsilon > 0$, depending only on the fixed types and turn weights, with the following property. For every fixed positive integer $K$, fixed real $C \ge 1$, and fixed nonnegative integer $I$, the conditional probability tends to zero that there exists a system as above having at most $K$ paths, total length $H$ with $L \le H \le CL$, at most $I$ interval pairs, and $b$ unpaired occurrences, where $b \le \varepsilon H$.” The proof (pp. 7–14) ends: “Finally there are $\exp(o(L))$ enlarged patterns and $H \ge L$. The union bound is at most $\exp(o(L) - \delta L/(4M))$, which tends to zero.”
--
--   **Formalization note.** The objects are OpenAI's (`BoundedPattern.Data`, `Data.Good`, `Data.event`, `PatternUniform.Ready`, `PatternTotalCoding.coefficient`, `ActualPatternEvent.samples`, from the bundle `Def_TorsionFreeZeroDivisorsConstruction`). The bound is OpenAI's explicit form, $e^{-L/(4800M)}$, with $\varepsilon=1/2467200$ built into goodness. Readiness is a list of explicit numerical inequalities in $L$, $B$, $M$, $Q$ and $J$. The inversion of letters goes through one fixed, unspecified bijection (`Fintype.equivOfCardEq`); the paper pairs the letters “arbitrarily”.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, p. 7, Proposition 3.1 (bounded-pattern estimate), in the quantitative union-bound form of its proof (pp. 7-14); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), BoundedPattern.probability_union

import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Mathlib

namespace OAI.TorsionFreeZeroDivisors.BoundedPattern

open scoped Classical
open ActualPatternEvent GirthAsymptotics TypedGraphs

theorem probability_union (R K T I H B Q M J rep : ℕ)
    (hR : 0<R) (hK : 0<K) (hI : 0<I) (hM : 0<M)
    (hs : (samples rep).Nonempty) (hready : PatternUniform.Ready B M Q J rep)
    (x : Types.VertexA rep) (y : Types.VertexB rep) :
    (((samples rep).filter (fun r => ∃ a : Data R K T I H,a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ)/
      (samples rep).card≤
      (PatternTotalCoding.coefficient R K T I:ℝ)*(H+1:ℕ)^(R+3*I)*
        Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  sorry

end OAI.TorsionFreeZeroDivisors.BoundedPattern
