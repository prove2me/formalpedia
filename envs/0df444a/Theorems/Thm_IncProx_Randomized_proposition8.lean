-- Prove2me | Theorems.Thm_IncProx_Randomized_proposition8
-- name    : IncProx.Randomized.proposition8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:33.308992+00:00
-- url     : https://prove2.me/theorems/053cc41f-000e-4f36-a478-12c6af6775bd
-- title:
--   Proposition 8 — $\min_{0\le k\le N}F(x_k)\le F^*+(\alpha\beta mc^2+\epsilon)/2$ a.s., with $E\{N\}\le m\,\mathrm{dist}(x_0;X^*)^2/(\alpha\epsilon)$
-- statement:
--   Let $x_k$ be generated as in Proposition 7 (one of the randomized methods (42)–(44), constant stepsize $\alpha>0$, Assumption 3 or 4 with constant $c$), assume that $X^*$ is nonempty, and let $\epsilon>0$. Let
--   $$L=\Bigl\{x\in X\ \Bigm|\ F(x)<F^*+\frac{\alpha\beta mc^2+\epsilon}{2}\Bigr\},\qquad\beta=5,$$
--   and let $N=\min\{k\ge0\mid x_k\in L\}$ be the first iteration at which the run enters $L$ ($N=\infty$ if it never does). Then $N$ is a random variable, with probability 1
--   $$\min_{0\le k\le N}F(x_k)\le F^*+\frac{\alpha\beta mc^2+\epsilon}{2},\qquad(54)$$
--   and
--   $$E\{N\}\le m\,\frac{\mathrm{dist}(x_0;X^*)^2}{\alpha\epsilon}.\qquad(55)$$
--
--   The bound (55) is on the expected number of iterations needed to reach the error tolerance, to be compared with the deterministic count of Proposition 5 for the cyclic order.
--
--   **Formalization Note** The paper writes "where $N$ is a random variable with (55)"; an arbitrary $N$ would make the statement nearly empty ($N=0$ satisfies (55) whenever (54) holds at $k=0$), so $N$ is the paper's own random variable from the proof of Proposition 8 (p. 19): the first index $k$ with $x_k\in L$, valued in $\mathbb N\cup\{\infty\}$. With probability 1 it is finite, and (54) is stated as the existence of $k\le N$ with $F(x_k)$ below the bound. **Added hypothesis:** the starting point lies in $X$. The proof applies Eq. (50) at $k=0$, which for (42) and (44) uses $x_0=P_X(x_0)$; the paper does not state this. $\mathrm{dist}(x_0;X^*)$ is `Metric.infDist`, $F^*$ is the extended-real optimal value (finite since $X^*\neq\emptyset$), and $E\{N\}$ is the lower Lebesgue integral of $N$ in $[0,\infty]$.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), p. 19, Proposition 8 (L and N from its proof, p. 19)

import Mathlib
import Definitions.Def_IncProx_Randomized_Basic

namespace IncProx.Randomized

open Filter Topology MeasureTheory

/-- Proposition 8 (p. 19), for a run as in Proposition 7 started inside X: assume X* ≠ ∅ and
ε > 0, and let N be the first k with x_k in the level set
L = {x ∈ X | F(x) < F* + (αβmc² + ε)/2}, β = 5 (proof of Prop. 8, p. 19). Then N is a random
variable; with probability 1, N < ∞ and min_{0≤k≤N} F(x_k) ≤ F* + (αβmc² + ε)/2 (54); and
E{N} ≤ m dist(x₀; X*)²/(αε) (55). The hypothesis x₀ ∈ X is added. -/
theorem proposition8 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Problem n m) (hP : P.Standing) (A : Alg)
    (α : ℝ) (hα : 0 < α) (ω : ℕ → Ω → Fin m) (x : ℕ → Ω → Vec n)
    (zc gFc gHc xc : ℕ → Fin m → Ω → Vec n) (x₀ : Vec n) (c : ℝ)
    (hR : RandHyp μ P A (fun _ => α) ω x zc gFc gHc xc x₀ c)
    (hx₀ : x₀ ∈ P.X) (hXstar : P.Xstar.Nonempty) (ε : ℝ) (hε : 0 < ε) :
    let L : Set (Vec n) :=
      {y | y ∈ P.X ∧ ((P.F y : ℝ) : EReal) < P.Fstar + (((α * 5 * m * c ^ 2 + ε) / 2 : ℝ) : EReal)}
    let N : Ω → ℕ∞ := firstHit x L
    Measurable N ∧
      (∀ᵐ s ∂μ, N s ≠ ⊤ ∧ ∃ k : ℕ, (k : ℕ∞) ≤ N s ∧
        ((P.F (x k s) : ℝ) : EReal) ≤ P.Fstar + (((α * 5 * m * c ^ 2 + ε) / 2 : ℝ) : EReal)) ∧
      ∫⁻ s, ENat.toENNReal (N s) ∂μ ≤
        ENNReal.ofReal (m * Metric.infDist x₀ P.Xstar ^ 2 / (α * ε)) := by sorry

end IncProx.Randomized
