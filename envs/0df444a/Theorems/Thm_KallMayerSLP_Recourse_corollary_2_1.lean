-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_corollary_2_1
-- name    : KallMayerSLP.Recourse.corollary_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:36.985002+00:00
-- url     : https://prove2.me/theorems/ed2431d3-bd3a-4dd2-ad1c-f32d9057b8e9
-- title:
--   Corollary 2.1 — the conclusions of Theorem 2.3 under independence and $\xi\in L^1$
-- statement:
--   Throughout, $\xi$ is a random vector in $\mathbb R^r$ with distribution $\mathbb P_\xi$ and support $\Xi=\operatorname{supp}\mathbb P_\xi$ (the smallest closed set of probability one); the second-stage data $T(\xi),h(\xi),q(\xi)$ are affine in $\xi$ as in (2.1), and the recourse matrix $W\in\mathbb R^{m_2\times n_2}$ is fixed. The **recourse function** is the optimal value of the second-stage LP (2.9),
--
--   $$
--   Q(x;T(\xi),h(\xi),q(\xi))=\min\{q^{\mathsf T}(\xi)y \mid Wy=h(\xi)-T(\xi)x,\ y\ge 0\},
--   $$
--
--   with value $+\infty$ when the LP is infeasible and $-\infty$ when it is unbounded. **Assumption 2.1** (complete fixed recourse, (2.6)): $\{z\mid z=Wy,\ y\ge 0\}=\mathbb R^{m_2}$. **Assumption 2.2** ((2.8)): $\{u\mid W^{\mathsf T}u\le q(\xi)\}\neq\emptyset$ for every $\xi\in\Xi$.
--
--   Assume Assumptions 2.1 and 2.2, and, instead of $\xi\in L^2$, that $\xi\in L^1(\Omega,\mathbb R^r)$ and that the random entries $q(\xi)$ and $(h(\xi),T(\xi))$ are stochastically independent. Then the **expected recourse**
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
--   Independence of the cost from the right-hand side and technology lets first moments replace second moments, because the recourse function is bilinear in $q(\xi)$ and $(h(\xi),T(\xi))$ on each decision region.
--
--   **Formalization Note** Independence is `IndepFun` under $\mu=\mathbb P_\xi$ of $\xi\mapsto q(\xi)$ and $\xi\mapsto(h(\xi),T(\xi))$, with $T(\xi)$ as its array of entries. The conclusion is that of Theorem 2.3 word for word.
--
--   Differences from the source:
--   - encoding: probability space (Ω, ℱ, P) with ℱ = σ(ξ) and the induced distribution ℙ_ξ on ℝʳ → a probability measure μ = ℙ_ξ on `Fin r → ℝ` (canonical space, ξ = id); reason: the statement involves ξ only through ℙ_ξ; same instances
--   - encoding: Ξ = supp ℙ_ξ, the smallest closed set with ℙ_ξ(Ξ) = 1 → `μ.support` (Mathlib's support: points all of whose neighbourhoods have positive measure); reason: the two sets coincide in ℝʳ
--   - encoding: T(ξ), h(ξ), q(ξ) affine in ξ by (2.1), W(ξ) ≡ W fixed → `RandomData` with fields T0, Tj, h0, hj, q0, qj and one fixed matrix W; reason: notation only
--   - encoding: recourse value Q(x; T(ξ), h(ξ), q(ξ)) as an inf with values ±∞ → the published `KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum (+∞ if infeasible, −∞ if unbounded); reason: the book's convention of p.200; same values
--   - encoding: 𝒬(x) = ∫_Ξ Q(x; T(ξ), h(ξ), q(ξ)) ℙ_ξ(dξ) finitely valued → Q(x; ξ) finite μ-a.e., its real part integrable (with measurability), and 𝒬 = the published `KallMayer.Recourse.ExpectedRecourse` (Bochner integral of the real part); reason: this is what a finite Lebesgue integral of an extended-real function means
--   - encoding: the norm ‖x⁽¹⁾ − x⁽²⁾‖ → the Euclidean norm `‖WithLp.toLp 2 (x₁ - x₂)‖`; reason: the book's ‖·‖ on ℝ^{n₁}
--   - generalization: clause a) for x ∈ B₁ = {x | Ax = b, x ≥ 0} → every x ∈ ℝ^{n₁}; reason: Assumption 2.1 makes the second-stage LP feasible for every x (proof of a)); B₁ ⊂ ℝ^{n₁}, so the statement specializes to the book's
--   - encoding: q(ξ) and (h(ξ), T(ξ)) stochastically independent; ξ ∈ L¹ → `IndepFun (fun ξ => D.q ξ) (fun ξ => (D.h ξ, fun i j => D.T ξ i j)) μ`; `Integrable id μ`; reason: same conditions
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Corollary 2.1, p.209 (PDF 218)

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayer_Recourse_ExpectedRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData

open MeasureTheory ProbabilityTheory
open KallMayer.Recourse (CompleteRecourse PointwiseRecourse ExpectedRecourse)
open Matrix

namespace KallMayerSLP.Recourse

/-- Corollary 2.1 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Corollary 2.1,
p.209, PDF 218): given that, instead of `ξ ∈ L²(Ω, ℝʳ)`, the random entries `q(ξ)` and
`(h(ξ), T(ξ))` are stochastically independent and `ξ ∈ L¹(Ω, ℝʳ)`, the conclusions of Th. 2.3 hold
true, as well.

**Formalization Note.** Same setting as `theorem_2_3` (`μ = ℙ_ξ` on `ℝʳ`, `Ξ = μ.support`,
Assumptions 2.1 and 2.2), with `MemLp id 2 μ` replaced by `Integrable id μ` and independence of the
random vectors `ξ ↦ q(ξ)` and `ξ ↦ (h(ξ), T(ξ))` under `μ` (`T(ξ)` as its array of entries).
The conclusion is that of `theorem_2_3`, verbatim. -/
theorem corollary_2_1 {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hξ : Integrable id μ)
    (hind : IndepFun (fun ξ => D.q ξ) (fun ξ => (D.h ξ, fun i j => D.T ξ i j)) μ)
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
