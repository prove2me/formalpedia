-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_lemma_2_2
-- name    : KallMayerSLP.Recourse.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:28.925145+00:00
-- url     : https://prove2.me/theorems/f6432aaa-f7b9-4a86-9216-5f53e2d7e74b
-- title:
--   Lemma 2.2 — an optimal recourse in $L^2$ exists
-- statement:
--   Throughout, $\xi$ is a random vector in $\mathbb R^r$ with distribution $\mathbb P_\xi$ and support $\Xi=\operatorname{supp}\mathbb P_\xi$ (the smallest closed set of probability one); the second-stage data $T(\xi),h(\xi),q(\xi)$ are affine in $\xi$ as in (2.1), and the recourse matrix $W\in\mathbb R^{m_2\times n_2}$ is fixed. The **recourse function** is the optimal value of the second-stage LP (2.9),
--
--   $$
--   Q(x;T(\xi),h(\xi),q(\xi))=\min\{q^{\mathsf T}(\xi)y \mid Wy=h(\xi)-T(\xi)x,\ y\ge 0\},
--   $$
--
--   with value $+\infty$ when the LP is infeasible and $-\infty$ when it is unbounded. **Assumption 2.1** (complete fixed recourse, (2.6)): $\{z\mid z=Wy,\ y\ge 0\}=\mathbb R^{m_2}$. **Assumption 2.2** ((2.8)): $\{u\mid W^{\mathsf T}u\le q(\xi)\}\neq\emptyset$ for every $\xi\in\Xi$.
--
--   Assume in addition the standing assumption $\xi\in L^2(\Omega,\mathbb R^r)$ (p.199) and let $Y=L^2(\Omega,\mathbb R^{n_2})$ be the space of second-stage decisions. Under Assumptions 2.1 and 2.2, for every first-stage decision $x\in\mathbb R^{n_1}$ there is an optimal recourse $y(\cdot)\in Y$:
--
--   $$
--   Wy(\xi)=h(\xi)-T(\xi)x,\quad y(\xi)\ge 0,\quad Q(x;T(\xi),h(\xi),q(\xi))=q^{\mathsf T}(\xi)\,y(\xi)\qquad\text{for all }\xi\in\Xi .
--   $$
--
--   The content is the **measurability and square integrability** of an optimal selection, which is what makes the two-stage problem (2.3) with $y(\cdot)\in Y$ equivalent to minimizing $c^{\mathsf T}x$ plus the expected recourse.
--
--   **Formalization Note** The probability space is the canonical one: $\Omega=\mathbb R^r$, $\xi$ the identity and $\mathcal F=\sigma(\xi)$ the Borel sets, so $Y$ is the set of $y:\mathbb R^r\to\mathbb R^{n_2}$ with `MemLp y 2 μ`, $\mu=\mathbb P_\xi$.
--
--   Differences from the source:
--   - encoding: probability space (Ω, ℱ, P) with ℱ = σ(ξ) and the induced distribution ℙ_ξ on ℝʳ → a probability measure μ = ℙ_ξ on `Fin r → ℝ` (canonical space, ξ = id); reason: the statement involves ξ only through ℙ_ξ; same instances
--   - encoding: Ξ = supp ℙ_ξ, the smallest closed set with ℙ_ξ(Ξ) = 1 → `μ.support` (Mathlib's support: points all of whose neighbourhoods have positive measure); reason: the two sets coincide in ℝʳ
--   - encoding: T(ξ), h(ξ), q(ξ) affine in ξ by (2.1), W(ξ) ≡ W fixed → `RandomData` with fields T0, Tj, h0, hj, q0, qj and one fixed matrix W; reason: notation only
--   - encoding: recourse value Q(x; T(ξ), h(ξ), q(ξ)) as an inf with values ±∞ → the published `KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum (+∞ if infeasible, −∞ if unbounded); reason: the book's convention of p.200; same values
--   - encoding: Y = L²(Ω, ℝ^{n₂}) with ℱ = σ(ξ) → y : ℝʳ → ℝ^{n₂} with `MemLp y 2 μ`; reason: σ(ξ)-measurable maps are functions of ξ (Doob–Dynkin); same objects
--   - reading: 'optimal recourse y(·) ∈ Y such that Q(x; T(ξ), h(ξ), q(ξ)) = qᵀ(ξ)y(ξ)' (no quantifier on ξ) → y(ξ) feasible for (2.9) and attaining Q, for every ξ ∈ Ξ; reason: the proof constructs y on the partition of Ξ; the pointwise reading is the stronger one
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.2, p.204 (PDF 213); setting pp.198–203 (PDF 207–212)

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData

open MeasureTheory
open KallMayer.Recourse (CompleteRecourse PointwiseRecourse)
open Matrix

namespace KallMayerSLP.Recourse

/-- Lemma 2.2 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.2, p.204,
PDF 213): given Assumptions 2.1 and 2.2, for any `x ∈ ℝ^{n₁}` there exists an optimal recourse
`y(·) ∈ Y = L²(Ω, ℝ^{n₂})` such that `Q(x; T(ξ), h(ξ), q(ξ)) = qᵀ(ξ) y(ξ)`.

Setting (pp.198–203): `μ = ℙ_ξ` is the distribution of `ξ` on `ℝʳ`, `ξ ∈ L²` (p.199), the data are
affine in `ξ` (2.1), the recourse matrix `W` is fixed, Assumption 2.1 is complete recourse (2.6), and
Assumption 2.2 is `{u | Wᵀ u ≤ q(ξ)} ≠ ∅` for all `ξ ∈ Ξ = supp ℙ_ξ` (2.8).

**Formalization Note.** The probability space is the canonical one, `Ω = ℝʳ` with `ξ = id` and
`ℱ = σ(ξ)` = Borel sets, so `Y = L²(Ω, ℝ^{n₂})` is `MemLp y 2 μ` for `y : ℝʳ → ℝ^{n₂}`. "Optimal
recourse" is read pointwise on the support: `y(ξ)` is feasible for (2.9) and attains its value, for
every `ξ ∈ Ξ` (this is what the proof constructs). The recourse function is the published
`KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum. -/
theorem lemma_2_2 {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hξ : MemLp id 2 μ)
    (hW : CompleteRecourse W)
    (hdual : ∀ ξ ∈ μ.support, ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q ξ)
    (x : Fin n₁ → ℝ) :
    ∃ y : (Fin r → ℝ) → (Fin n₂ → ℝ), MemLp y 2 μ ∧
      ∀ ξ ∈ μ.support, W *ᵥ y ξ = D.h ξ - D.T ξ *ᵥ x ∧ 0 ≤ y ξ ∧
        PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x = ((D.q ξ ⬝ᵥ y ξ : ℝ) : EReal) := by sorry

end KallMayerSLP.Recourse
