-- Prove2me | Theorems.Thm_GarberOLO_Alg3_lemma5
-- name    : GarberOLO.Alg3.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:02:42.002196+00:00
-- url     : https://prove2.me/theorems/05ab0d63-10bf-475c-b352-74544834a8eb
-- title:
--   Lemma 5: Separation-or-Decomposition via the Ellipsoid method
-- statement:
--   Throughout, $K, \mathcal F \subset \mathbb R^d_+$ are compact, $\|x\| \le R$ on $K$, $\|f\| \le F$ on $\mathcal F$, $0 \le x\cdot f \le C$ on $K \times \mathcal F$ ($R, F, C > 0$), and $\mathcal O_K$ is an $\alpha$-approximate linear optimization oracle for $K$ ($\alpha > 0$; §2.1).
--
--   There is a universal constant $c_0 > 0$ such that the following holds. Let $x \in \mathbb R^d$, $\varepsilon \in (0, (\alpha+2)R]$ and let $N$ be a positive integer with
--   $$N \ge c_0\, d^2 \ln\frac{(\alpha+1)R + \|x\|}{\varepsilon}.$$
--   Run the Separation-or-Decomposition procedure (the Ellipsoid method on Problem (4), at most $N$ iterations, steps 1–3 of Lemma 5) at $x$. Then:
--
--   1. if it returns a vector $w$, then $w$ is feasible for Problem (4): $\|w\| \le 1$ and $(x - z)\cdot w \ge \varepsilon$ for every $z \in \alpha K$;
--   2. if it completes $N$ iterations, with oracle outputs $(v_1, s_1), \dots, (v_N, s_N)$, then for every optimal solution $(a_1, \dots, a_N)$ of Problem (5) the point $p = \sum_i a_i v_i$ satisfies $\|x - p\| \le 3\varepsilon$.
--
--   With $O(d^2 \log)$ oracle calls one either separates $x$ from $\mathrm{CH}(\alpha K)$ with margin $\varepsilon$ or finds a convex combination of oracle outputs within $3\varepsilon$ of $x$.
--
--   Differences from the source:
--   - encoding: c is a positive universal constant; O(·) → the constants are quantified before the dimension d and every datum of the instance; reason: this is what "universal" and O(·) mean; constants chosen after the instance would make the bounds trivial
--   - reading: "the Ellipsoid method" (Lemma 5, p. 9), not specified further → the central-cut Ellipsoid method from E₀ = B(0,1) (ellipsoidCut, sdState), with bisection for d = 1 and no change on a zero cut vector; reason: E₀ = B(0,1) is the ball of Problem (4)'s constraint, which the proof on p. 11 needs (B(h/2, r) ⊂ B(0,1)); the standard update divides by d² − 1 = 0 when d = 1; a zero cut arises only when v = x, and then p = x (paper.md Reading 1)
--   - reading: "(a₁, …, a_N) be an optimal solution" of Problem (5) → every a with IsOptimal5 x v a; reason: the paper takes an arbitrary optimal solution (paper.md Reading 5)
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, pp. 9–10

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_IsApproxOracle
import Definitions.Def_GarberOLO_Alg3_IsOptimal5
import Definitions.Def_GarberOLO_Alg3_sepOrDec

open scoped RealInnerProductSpace Pointwise

namespace GarberOLO.Alg3

/-- **Lemma 5 (Separation-or-Decomposition via the Ellipsoid method).**
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, pp. 9–10: "Fix x ∈ ℝᵈ, ε ∈ (0, (α + 2)R], and a positive integer
N ≥ cd² ln(((α+1)R+‖x‖)/ε), where c is a positive universal constant. Consider an attempt to apply
the Ellipsoid method for N iterations to the following feasibility problem: find w ∈ ℝᵈ such that:
∀ z ∈ αK : (x − z) · w ≥ ε, ‖w‖ ≤ 1, (4) … Then, if the Ellipsoid method terminates declaring
Problem 4 feasible, the returned vector w is a feasible solution to Problem (4). Otherwise …,
let (v₁, s₁), …, (v_N, s_N) be the outputs of the extended approximation oracle gathered throughout
the run of the algorithm, and let (a₁, …, a_N) be an optimal solution to [Problem (5)]. Then the
point p = Σ_{i=1}^N aᵢvᵢ satisfies ‖x − p‖ ≤ 3ε."

There is a constant `c₀ > 0` such that, for every instance of the setting with an oracle
satisfying the §2.1 guarantee, every `x`, every `ε ∈ (0, (α+2)R]` and every positive integer
`N ≥ c₀ d² ln(((α+1)R + ‖x‖)/ε)`, the procedure `sepOrDec S OK x ε N` satisfies:
(i) if it returns a vector `w`, then `‖w‖ ≤ 1` and `ε ≤ ⟪x − z, w⟫` for every `z ∈ αK`;
(ii) if it returns a decomposition `(vᵢ, sᵢ)`, then `‖x − Σᵢ aᵢvᵢ‖ ≤ 3ε` for every optimal
solution `a` of Problem (5) for `(x, v)`.

**Formalization Note.** The universal constant comes first (`∃ c₀` before the dimension and
every datum), so it depends on nothing. The Ellipsoid method is the central-cut method from
B(0, 1) of `ellipsoidCut`/`sdState` (Reading 1). -/
theorem lemma5 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d : ℕ} (S : Setting d) (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsApproxOracle S OK →
      ∀ (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ), 0 < ε → ε ≤ (S.α + 2) * S.R →
      ∀ N : ℕ, 0 < N →
        c₀ * (d : ℝ) ^ 2 * Real.log (((S.α + 1) * S.R + ‖x‖) / ε) ≤ (N : ℝ) →
        ((sepOrDec S OK x ε N).isSep = true →
            ‖(sepOrDec S OK x ε N).w‖ ≤ 1 ∧
            ∀ z ∈ S.α • S.K, ε ≤ ⟪x - z, (sepOrDec S OK x ε N).w⟫) ∧
        ((sepOrDec S OK x ε N).isSep = false →
            ∀ a : Fin N → ℝ, IsOptimal5 x (fun i => ((sepOrDec S OK x ε N).vs i).1) a →
              ‖x - ∑ i, a i • ((sepOrDec S OK x ε N).vs i).1‖ ≤ 3 * ε) := by sorry

end GarberOLO.Alg3
