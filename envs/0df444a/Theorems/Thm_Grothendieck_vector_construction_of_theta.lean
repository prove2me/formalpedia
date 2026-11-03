-- Prove2me | Theorems.Thm_Grothendieck_vector_construction_of_theta
-- name    : Grothendieck.vector_construction_of_theta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:32:22.490758+00:00
-- url     : https://prove2.me/theorems/4630f008-8089-4952-8727-9f72ac70faf0
-- title:
--   Lemma 4.1 reduced to the theta program and the beta-series analysis
-- statement:
--   Lemma 4.1 of the paper is the step that linearizes the rounding argument. Given a graph $G=(V,E)$ with at least one edge, a rank $r\ge1$, and any $f:V\to S^{|V|-1}$, it produces $g:V\to S^{|V|-1}$ with
--
--   $$
--   E_r\big(g(u)\cdot g(v)\big)=\beta(r,G)\,\big(f(u)\cdot f(v)\big)
--   $$
--
--   for every edge $\{u,v\}$ — so that the Gaussian rounding of $g$ has expectation exactly proportional to the value of $f$, edge by edge, which is what turns the algorithm's analysis into a constant-factor guarantee.
--
--   This node records the reduction proved by the paper's argument, with the analytic inputs isolated as explicit hypotheses rather than assumed silently:
--
--   1. $2\le\vartheta(G)$ (which holds for any graph with an edge);
--   2. the convergence statement of Proposition 4.2, $E_r^{-1}(t\,\beta(r,G))=\sum_k b_{2k+1}(t\,\beta(r,G))^{2k+1}$ for $|t|\le1$;
--   3. summability of the series with absolute values at $\beta(r,G)$ and at every larger $t$;
--   4. that $\beta(r,G)$ is attained, i.e. lies in the set of $t\ge0$ with $\sum_k|b_{2k+1}|t^{2k+1}\ge 1/(\vartheta(G)-1)$;
--   5. $|\beta(r,G)|\le E_r(1)$;
--   6. an *optimal* solution $Z$ of the theta program (4.1), not merely a feasible one.
--
--   Under these, the conclusion is Lemma 4.1 as stated. The construction is Krivine's: build the Hilbert-space vectors $S(x),T(x)$ from the absolute Taylor coefficients so that $S(x)\cdot T(y)=E_r^{-1}(\beta\,x\cdot y)$, use the theta program to produce two vector families with inner products $0$ across edges and $1/2$ between the two families, combine them, and read off the Gram matrix.
--
--   **Formalization Note** A reduction, not a proof of the leaf `Grothendieck.vector_construction`: hypotheses 2, 3 and 5 are the paper's Proposition 4.2 and the beta-series analysis, and hypothesis 6 is the attainment of the theta optimum, which the mission's `thetaComplement` (an infimum) does not carry by itself.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 4.1, p. 92, proof pp. 94-95.

import Mathlib
import Definitions.Def_Grothendieck_Beta

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 4.1 as a reduction.** Given the analytic facts about the theta program and about
`β(r,G)` listed as hypotheses, the vector construction of Lemma 4.1 holds: every
`f : V → S^{|V|-1}` is pushed to `g : V → S^{|V|-1}` with
`E_r(g u · g v) = β(r,G) · (f u · f v)` across every edge. -/
theorem vector_construction_of_theta (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V)
    (hne : ∃ u v, G.Adj u v) (f : V → EuclideanSpace ℝ V) (hf : ∀ v, ‖f v‖ = 1)
    (hϑ : 2 ≤ thetaComplement G)
    (hser : ∀ t : ℝ, |t| ≤ 1 →
      Summable (fun k : ℕ => invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) ∧
        (∑' k : ℕ, invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) =
          ErInv r (t * beta r G))
    (habs : Summable (fun k : ℕ => |invCoeff r (2 * k + 1)| * (beta r G) ^ (2 * k + 1)))
    (hneβ : ∃ t : ℝ, 0 ≤ t ∧ 1 / (thetaComplement G - 1) ≤ betaSeries r t)
    (hsumβ : ∀ t : ℝ, beta r G < t →
      Summable fun k : ℕ => |invCoeff r (2 * k + 1)| * t ^ (2 * k + 1))
    (hβR : |beta r G| ≤ Er r 1)
    (hZ : ∃ Z : Matrix V V ℝ, Z.PosSemidef ∧ (∀ u, Z u u = thetaComplement G - 1) ∧
      ∀ u v, G.Adj u v → Z u v = -1) :
    ∃ g : V → EuclideanSpace ℝ V, (∀ v, ‖g v‖ = 1) ∧
      ∀ u v, G.Adj u v → Er r (inner ℝ (g u) (g v)) = beta r G * inner ℝ (f u) (f v) := by sorry

end Grothendieck
