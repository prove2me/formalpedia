-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_theorem_2_3
-- name    : KallMayerSLP.Recourse.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:34.032477+00:00
-- url     : https://prove2.me/theorems/64cd4ce1-2961-4018-b10f-dfd81da88470
-- title:
--   Theorem 2.3 — under complete fixed recourse the expected recourse is finite, convex and Lipschitz
-- statement:
--   Throughout, $\xi$ is a random vector in $\mathbb R^r$ with distribution $\mathbb P_\xi$ and support $\Xi=\operatorname{supp}\mathbb P_\xi$ (the smallest closed set of probability one); the second-stage data $T(\xi),h(\xi),q(\xi)$ are affine in $\xi$ as in (2.1), and the recourse matrix $W\in\mathbb R^{m_2\times n_2}$ is fixed. The **recourse function** is the optimal value of the second-stage LP (2.9),
--
--   $$
--   Q(x;T(\xi),h(\xi),q(\xi))=\min\{q^{\mathsf T}(\xi)y \mid Wy=h(\xi)-T(\xi)x,\ y\ge 0\},
--   $$
--
--   with value $+\infty$ when the LP is infeasible and $-\infty$ when it is unbounded. **Assumption 2.1** (complete fixed recourse, (2.6)): $\{z\mid z=Wy,\ y\ge 0\}=\mathbb R^{m_2}$. **Assumption 2.2** ((2.8)): $\{u\mid W^{\mathsf T}u\le q(\xi)\}\neq\emptyset$ for every $\xi\in\Xi$.
--
--   Assume Assumptions 2.1 and 2.2 and that $\xi\in L^2(\Omega,\mathbb R^r)$, i.e. $\xi$ is square integrable with respect to $\mathbb P_\xi$. Then the **expected recourse**
--
--   $$
--   \mathcal Q(x)=\int_\Xi Q(x;T(\xi),h(\xi),q(\xi))\,\mathbb P_\xi(d\xi)
--   $$
--
--   satisfies:
--
--   1. for every $x\in\mathbb R^{n_1}$, $\mathcal Q(x)$ is finite: $Q(x;T(\xi),h(\xi),q(\xi))$ is finite for $\mathbb P_\xi$-almost every $\xi$ and integrable;
--   2. $\mathcal Q$ is convex on $\mathbb R^{n_1}$;
--   3. $\mathcal Q$ is Lipschitz continuous: there is $L$ with $|\mathcal Q(x^{(1)})-\mathcal Q(x^{(2)})|\le L\,\|x^{(1)}-x^{(2)}\|$ for all $x^{(1)},x^{(2)}\in\mathbb R^{n_1}$.
--
--   Hence the two-stage problem (2.3), minimize $c^{\mathsf T}x+\mathcal Q(x)$ subject to $Ax=b$, $x\ge 0$, is a convex optimization problem with a Lipschitz continuous objective. This is the basic well-posedness result for two-stage stochastic linear programs with a general (not necessarily discrete) distribution.
--
--   **Formalization Note** $\mathcal Q$ is the published `KallMayer.Recourse.ExpectedRecourse`, the Bochner integral of the real part of the `EReal` recourse value; clause 1 makes this a genuine finite integral. $\|\cdot\|$ is the Euclidean norm.
--
--   Differences from the source:
--   - encoding: probability space (Ω, ℱ, P) with ℱ = σ(ξ) and the induced distribution ℙ_ξ on ℝʳ → a probability measure μ = ℙ_ξ on `Fin r → ℝ` (canonical space, ξ = id); reason: the statement involves ξ only through ℙ_ξ; same instances
--   - encoding: Ξ = supp ℙ_ξ, the smallest closed set with ℙ_ξ(Ξ) = 1 → `μ.support` (Mathlib's support: points all of whose neighbourhoods have positive measure); reason: the two sets coincide in ℝʳ
--   - encoding: T(ξ), h(ξ), q(ξ) affine in ξ by (2.1), W(ξ) ≡ W fixed → `RandomData` with fields T0, Tj, h0, hj, q0, qj and one fixed matrix W; reason: notation only
--   - encoding: recourse value Q(x; T(ξ), h(ξ), q(ξ)) as an inf with values ±∞ → the published `KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum (+∞ if infeasible, −∞ if unbounded); reason: the book's convention of p.200; same values
--   - encoding: 𝒬(x) = ∫_Ξ Q(x; T(ξ), h(ξ), q(ξ)) ℙ_ξ(dξ) finitely valued → Q(x; ξ) finite μ-a.e., its real part integrable (with measurability), and 𝒬 = the published `KallMayer.Recourse.ExpectedRecourse` (Bochner integral of the real part); reason: this is what a finite Lebesgue integral of an extended-real function means
--   - encoding: the norm ‖x⁽¹⁾ − x⁽²⁾‖ → the Euclidean norm `‖WithLp.toLp 2 (x₁ - x₂)‖`; reason: the book's ‖·‖ on ℝ^{n₁}
--   - generalization: clause a) for x ∈ B₁ = {x | Ax = b, x ≥ 0} → every x ∈ ℝ^{n₁}; reason: Assumption 2.1 makes the second-stage LP feasible for every x (proof of a)); B₁ ⊂ ℝ^{n₁}, so the statement specializes to the book's
--   - reading: 'Hence, (2.3) is a convex optimization problem with a Lipschitz continuous objective function' → not restated; reason: it follows from a) and b) because the objective is cᵀx + 𝒬(x) and B₁ is convex; it adds no condition on 𝒬
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.3, pp.208–209 (PDF 217–218)

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayer_Recourse_ExpectedRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData

open MeasureTheory
open KallMayer.Recourse (CompleteRecourse PointwiseRecourse ExpectedRecourse)
open Matrix

namespace KallMayerSLP.Recourse

/-- Theorem 2.3 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.3, p.208,
PDF 217): since `ξ ∈ L²(Ω, ℝʳ)`, the expected recourse
`𝒬(x) = ∫_Ξ Q(x; T(ξ), h(ξ), q(ξ)) ℙ_ξ(dξ)` is
a) finitely valued `∀ x ∈ B₁`, and
b) a convex and Lipschitz continuous function in `x`.

The standing assumptions of §2.1 are in force: `W` fixed with complete recourse (Assumption 2.1,
(2.6)), `{u | Wᵀu ≤ q(ξ)} ≠ ∅` for every `ξ ∈ Ξ = supp ℙ_ξ` (Assumption 2.2, (2.8)), and the data
affine in `ξ` (2.1).

**Formalization Note.** `μ = ℙ_ξ` on `ℝʳ` (canonical space, `ξ = id`), `Ξ = μ.support`,
`ξ ∈ L²` is `MemLp id 2 μ`. The expected recourse is the published `KallMayer.Recourse.ExpectedRecourse`,
the Bochner integral of the real part of the `EReal` recourse value. Clause a) says that this integral
is a genuine finite integral: the recourse value is finite `μ`-a.e. and its real part is integrable
(including measurability); it is stated for every `x ∈ ℝ^{n₁}`, which contains the book's `x ∈ B₁`.
Clause b) is convexity on `ℝ^{n₁}` and a Lipschitz bound in the Euclidean norm. -/
theorem theorem_2_3 {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hξ : MemLp id 2 μ)
    (hW : CompleteRecourse W)
    (hdual : ∀ ξ ∈ μ.support, ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q ξ) :
    (∀ x : Fin n₁ → ℝ,
      (∀ᵐ ξ ∂μ, PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊥ ∧
          PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊤) ∧
        Integrable (fun ξ => (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal) μ) ∧
    ConvexOn ℝ Set.univ (ExpectedRecourse μ W D.T D.h D.q) ∧
    ∃ L : ℝ, ∀ x₁ x₂ : Fin n₁ → ℝ,
      |ExpectedRecourse μ W D.T D.h D.q x₁ - ExpectedRecourse μ W D.T D.h D.q x₂| ≤
        L * ‖WithLp.toLp 2 (x₁ - x₂)‖ := by sorry

end KallMayerSLP.Recourse
