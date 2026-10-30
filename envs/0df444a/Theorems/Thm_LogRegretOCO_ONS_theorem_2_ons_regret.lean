-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_theorem_2_ons_regret
-- name    : LogRegretOCO.ONS.theorem_2_ons_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:05:25.860312+00:00
-- url     : https://prove2.me/theorems/43a6f618-907a-4ff0-a651-8494bd2d7a7f
-- title:
--   Theorem 2 — Online Newton Step has regret at most $5(1/\alpha + GD)\, n \log T$ (corrected: $T \ge 2$)
-- statement:
--   Throughout, $\mathcal P \subseteq \mathbb R^n$ is convex and closed, $D > 0$ satisfies $\|y - z\|_2 \le D$ for all $y, z \in \mathcal P$, and $\alpha, G > 0$. The losses $f_1, f_2, \dots : \mathbb R^n \to \mathbb R$ are differentiable at every point of $\mathcal P$, satisfy $\|\nabla f_t(y)\|_2 \le G$ for $y \in \mathcal P$, and are $\alpha$-exp-concave on $\mathcal P$ (so in particular convex on $\mathcal P$). The points $x_1, x_2, \dots$ are a run of Online Newton Step (Fig. 2): $x_1 \in \mathcal P$ is arbitrary and
--   $$
--   x_{t+1} = \Pi_{\mathcal P}^{A_t}\Bigl(x_t - \tfrac{1}{\beta} A_t^{-1} \nabla_t\Bigr), \qquad t \ge 1,
--   $$
--   with $\nabla_t = \nabla f_t(x_t)$, $\beta = \tfrac12 \min\{\tfrac{1}{4GD}, \alpha\}$, $\varepsilon = \tfrac{1}{\beta^2 D^2}$, $A_t = \sum_{i=1}^t \nabla_i \nabla_i^\top + \varepsilon I_n$, and $\Pi_{\mathcal P}^{A}(y) = \operatorname{argmin}_{x \in \mathcal P} (y - x)^\top A (y - x)$.
--
--   Then for every horizon $T \ge 2$ and every comparator $u \in \mathcal P$,
--   $$
--   \sum_{t=1}^T \bigl(f_t(x_t) - f_t(u)\bigr) \le 5\Bigl(\frac{1}{\alpha} + GD\Bigr)\, n \log T .
--   $$
--   Here $\log$ is the natural logarithm. Equivalently, $\mathrm{Regret}_T(\mathrm{ONS}) = \sup_{f_1,\dots,f_T}\bigl[\sum_t f_t(x_t) - \min_{x \in \mathcal P}\sum_t f_t(x)\bigr] \le 5(\frac1\alpha + GD)\, n\log T$. This is the main result for Online Newton Step: for exp-concave losses a second-order online algorithm, running in $O(n^2)$ time per round plus a generalized projection, has regret logarithmic in $T$, against the $\Theta(\sqrt T)$ of online gradient descent for general convex losses.
--
--   Differences from the source:
--   - correction: Regret_T(ONS) ≤ 5(1/α + GD) n log T for every T → for every T ≥ 2; reason: at T = 1 the right side is 0, but n = 1, P = [0, 1] (D = 1), f_1(x) = −log(1 + x) (convex, twice differentiable, exp(−f_1) = 1 + x concave so α = 1, |f_1'| ≤ 1 = G) and x_1 = 0 give regret f_1(0) − f_1(1) = log 2 > 0; for T ≥ 2 the bound holds
--   - reading: f_t : P → Rⁿ → f_t real valued; reason: a misprint: costs are real (§2.1 p. 171, Lemma 3); the regret compares real values
--   - encoding: Regret_T(ONS) = sup over loss sequences of Σ f_t(x_t) − min_{x∈P} Σ f_t(x) → Σ (f_t(x_t) − f_t(u)) ≤ bound for every u ∈ P, every admissible loss sequence and every run; reason: ONS is deterministic (no expectation); a bound for every comparator u ∈ P is a bound against the minimizer, and the minimum is attained since P is compact and f_t continuous on P
--   - generalization: D is the diameter of P, D = max_{x,y∈P} ‖x − y‖₂ (p. 172) → any real D > 0 with ‖y − z‖ ≤ D for all y, z ∈ P, and ONS uses this D in β and ε; reason: the proof uses D only through ‖x_1 − x*‖ ≤ D and |∇f_t(y)ᵀ(x − y)| ≤ GD; taking D = diam P recovers the paper's statement whenever diam P > 0
--   - encoding: G and D positive implicitly (β = ½ min{1/(4GD), α} and ε = 1/(β²D²) divide by them) → hypotheses 0 < G and 0 < D; reason: the conditions only exclude the cases in which the paper's β and ε are undefined
--   - generalization: the losses are twice differentiable (standing assumption, p. 172) → f_t : ℝⁿ → ℝ differentiable at every point of P, with ∇f_t its gradient; reason: the proof of Theorem 2 (and of Lemma 3) uses only first derivatives; twice differentiable functions satisfy the hypothesis
--   - encoding: the losses are convex (standing assumption, pp. 171–172) → no separate convexity hypothesis; reason: convexity of f_t on P follows from α-exp-concavity with α > 0: −αf_t = log(exp(−αf_t)) is concave as the log of a positive concave function, so the hypothesis would be redundant
--   - generalization: exp(−αf_t(x)) is a concave function of x ∈ P, i.e. ∇²[exp(−αf_t(x))] ⪯ 0 (p. 173) → ConcaveOn ℝ P (fun x => exp(−α f_t x)); reason: the paper's first wording is concavity on P; its Hessian form implies ConcaveOn on the convex set P, but not conversely when P has empty interior
--   - encoding: P non-empty and bounded (standing assumption, p. 171) → no separate hypotheses; reason: non-emptiness follows from x_1 ∈ P (part of IsONSRun) and boundedness from the bound D on distances
--   - encoding: Fig. 2: x_t = Π_P^{A_{t−1}}(x_{t−1} − (1/β)A_{t−1}^{−1}∇_{t−1}) for t > 1, Π an argmin → IsONSRun: x_{t+1} satisfies IsGenProj (minimizer predicate) for A_t at x_t − β⁻¹ A_t⁻¹ ∇_t, for every t ≥ 1; A_t⁻¹ is Matrix.inv; reason: index shift t ↦ t + 1 as in the proof (x_{t+1} = Π^{A_t}(y_{t+1}), p. 177); A_t is positive definite (ε > 0), so Matrix.inv is the inverse; for P non-empty, closed, bounded the minimizer exists and is unique, so the paper's run is exactly a Lean run
--   - encoding: losses f_1, …, f_T for a horizon T → an infinite sequence f : ℕ → (ℝⁿ → ℝ) with the hypotheses for every t ≥ 1 (f_0, x_0 unused); reason: any finite sequence extends by f_t = 0 for t > T (0 satisfies every hypothesis) and the run extends because the generalized projection exists on the compact P; the statement for horizon T involves only f_1, …, f_T and x_1, …, x_{T+1}
--   - reading: ‖∇f(x)‖ ≤ G in the theorem's sentence → ‖∇f_t(y)‖₂ ≤ G for every t ≥ 1 and every y ∈ P; reason: p. 172 defines the gradient bound as sup_{x∈P, t∈[T]} ‖∇f_t(x)‖₂ ≤ G
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Theorem 2, p. 176 (PDF p. 8); algorithm Fig. 2, p. 176; proof pp. 177–179 (PDF pp. 9–11); standing assumptions §2.1–2.2, pp. 171–173 (PDF pp. 3–5)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_qform
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn
import Definitions.Def_LogRegretOCO_ONS_onsBeta
import Definitions.Def_LogRegretOCO_ONS_onsEps
import Definitions.Def_LogRegretOCO_ONS_onsGrad
import Definitions.Def_LogRegretOCO_ONS_onsA
import Definitions.Def_LogRegretOCO_ONS_IsGenProj
import Definitions.Def_LogRegretOCO_ONS_IsONSRun
open Matrix

namespace LogRegretOCO.ONS

/-- **Theorem 2 (regret of ONLINE NEWTON STEP; corrected: T ≥ 2).**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Theorem 2, p. 176; algorithm Fig. 2, p. 176; proof pp. 177–179:
"Assume that for all t, the loss function f_t : P → Rⁿ is α-exp-concave and has the property
that ∀x ∈ P, ‖∇f(x)‖ ≤ G. Then the algorithm ONLINE NEWTON STEP has the following regret bound:
Regret_T(ONS) ≤ 5(1/α + GD) n log T."

For every horizon `T ≥ 2` and every comparator `u ∈ P`:
`Σ_{t=1}^T (f_t(x_t) − f_t(u)) ≤ 5(1/α + GD) n log T`.

Common hypotheses (the standing assumptions of §2.1–2.2, pp. 171–173, and of Theorem 2):
`P ⊆ ℝⁿ` convex and closed; `D > 0` bounds the distance between any two points of `P`; `α > 0`,
`G > 0`; every loss `f_t` (`t ≥ 1`) is differentiable at every point of `P`, has
`‖∇f_t(y)‖₂ ≤ G` on `P` and is `α`-exp-concave on `P`; `x` is a run of ONS (Fig. 2) with
parameters `G, D, α`. `P` is non-empty because `x_1 ∈ P` and bounded because of the `D` bound.

**Formalization Note.** (1) The printed bound is false at `T = 1` (its right side is `0`, while
`n = 1`, `P = [0, 1]`, `f_1(x) = −log(1 + x)`, `α = G = D = 1`, `x_1 = 0` give regret
`log 2 > 0`); the statement is made for every `T ≥ 2`. (2) `D` is any positive bound on the
distances in `P` (the paper's diameter is one), and ONS uses this `D` in `β` and `ε`.
(3) `f_t : ℝⁿ → ℝ` is differentiable at the points of `P` (the printed codomain `Rⁿ` is a
misprint for `R`; the twice differentiability of p. 172 is not needed); convexity of `f_t` on
`P` follows from exp-concavity with `α > 0`. (4) Exp-concavity is `ConcaveOn` on `P`.
(5) `Regret_T(ONS)` (sup over loss sequences of the total loss minus the best fixed point in
hindsight) is stated for every loss sequence satisfying the hypotheses, every run and every
comparator `u ∈ P`. (6) Rounds are indexed from `1`. -/
theorem theorem_2_ons_regret {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin n))} {G D α : ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hPc : Convex ℝ P) (hPcl : IsClosed P)
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hα : 0 < α) (hG : 0 < G)
    (hdiff : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (f t) y)
    (hgrad : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ P, ‖gradient (f t) y‖ ≤ G)
    (hexp : ∀ t : ℕ, 1 ≤ t → IsExpConcaveOn α P (f t))
    (hrun : IsONSRun P G D α f x) :
    ∀ T : ℕ, 2 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤ 5 * (1 / α + G * D) * n * Real.log T := by sorry

end LogRegretOCO.ONS
