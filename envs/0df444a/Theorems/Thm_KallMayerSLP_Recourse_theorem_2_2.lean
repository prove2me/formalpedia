-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_theorem_2_2
-- name    : KallMayerSLP.Recourse.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:26.751037+00:00
-- url     : https://prove2.me/theorems/237c1275-eb44-4159-a91a-e32c2e6cf037
-- title:
--   Theorem 2.2 — the subdifferential of the recourse function in $x$
-- statement:
--   Throughout, $\xi$ is a random vector in $\mathbb R^r$ with distribution $\mathbb P_\xi$ and support $\Xi=\operatorname{supp}\mathbb P_\xi$ (the smallest closed set of probability one); the second-stage data $T(\xi),h(\xi),q(\xi)$ are affine in $\xi$ as in (2.1), and the recourse matrix $W\in\mathbb R^{m_2\times n_2}$ is fixed. The **recourse function** is the optimal value of the second-stage LP (2.9),
--
--   $$
--   Q(x;T(\xi),h(\xi),q(\xi))=\min\{q^{\mathsf T}(\xi)y \mid Wy=h(\xi)-T(\xi)x,\ y\ge 0\},
--   $$
--
--   with value $+\infty$ when the LP is infeasible and $-\infty$ when it is unbounded. **Assumption 2.1** (complete fixed recourse, (2.6)): $\{z\mid z=Wy,\ y\ge 0\}=\mathbb R^{m_2}$. **Assumption 2.2** ((2.8)): $\{u\mid W^{\mathsf T}u\le q(\xi)\}\neq\emptyset$ for every $\xi\in\Xi$.
--
--   Under Assumptions 2.1 and 2.2, for every $\xi\in\Xi$ the recourse function $x\mapsto Q(x;T(\xi),h(\xi),q(\xi))$ is subdifferentiable at every $\hat x\in\mathbb R^{n_1}$, and
--
--   $$
--   \partial_xQ(\hat x;T(\xi),h(\xi),q(\xi))=\bigl\{-T^{\mathsf T}(\xi)\hat u\ \bigm|\ \hat u\in\operatorname*{arg\,max}\{(h(\xi)-T(\xi)\hat x)^{\mathsf T}u\mid W^{\mathsf T}u\le q(\xi)\}\bigr\}.
--   $$
--
--   The subgradients of the recourse function are thus obtained from the optimal dual solutions of the second-stage LP, which is how cutting-plane methods generate cuts for two-stage problems.
--
--   **Formalization Note** The subdifferential is the published `StochasticProg.RecourseKKT.subdifferential` (finite value at $\hat x$, subgradient inequality against every $x$), and the argmax set is the published `KallMayer.Recourse.DualOptimizers`.
--
--   Differences from the source:
--   - encoding: probability space (Ω, ℱ, P) with ℱ = σ(ξ) and the induced distribution ℙ_ξ on ℝʳ → a probability measure μ = ℙ_ξ on `Fin r → ℝ` (canonical space, ξ = id); reason: the statement involves ξ only through ℙ_ξ; same instances
--   - encoding: Ξ = supp ℙ_ξ, the smallest closed set with ℙ_ξ(Ξ) = 1 → `μ.support` (Mathlib's support: points all of whose neighbourhoods have positive measure); reason: the two sets coincide in ℝʳ
--   - encoding: T(ξ), h(ξ), q(ξ) affine in ξ by (2.1), W(ξ) ≡ W fixed → `RandomData` with fields T0, Tj, h0, hj, q0, qj and one fixed matrix W; reason: notation only
--   - encoding: recourse value Q(x; T(ξ), h(ξ), q(ξ)) as an inf with values ±∞ → the published `KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum (+∞ if infeasible, −∞ if unbounded); reason: the book's convention of p.200; same values
--   - encoding: subdifferential of a convex function ℝⁿ → ℝ (Chapter 1, Def. 3.2, p.61); 'subdifferentiable at b' → the published `StochasticProg.RecourseKKT.subdifferential` of the `EReal` function (requires the value at the point to be finite); nonempty subdifferential; reason: the functions are finite here, where the two notions agree
--   - generalization: standing assumption ξ ∈ L²(Ω, ℝʳ) (p.199) → not assumed; reason: the statement is pointwise in ξ and does not use it; adding it back specializes to the book's
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.2, p.207 (PDF 216)

import Mathlib
import Definitions.Def_KallMayer_Recourse_LPValue
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential
import Definitions.Def_KallMayerSLP_Recourse_RandomData

open MeasureTheory
open KallMayer.Recourse (CompleteRecourse PointwiseRecourse DualOptimizers)
open StochasticProg.RecourseKKT (subdifferential)
open Matrix

namespace KallMayerSLP.Recourse

/-- Theorem 2.2 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.2, p.207,
PDF 216): given the Assumptions 2.1 and 2.2, the recourse function `Q(x; T(ξ), h(ξ), q(ξ))` is
subdifferentiable in `x` for any `ξ ∈ Ξ`. For any `x̂` holds
`∂ₓQ(x̂; T(ξ), h(ξ), q(ξ)) = {−Tᵀ(ξ)û | û ∈ argmax{(h(ξ) − T(ξ)x̂)ᵀu | Wᵀu ≤ q(ξ)}}` `∀ ξ ∈ Ξ`.

**Formalization Note.** `μ = ℙ_ξ` on `ℝʳ` and `Ξ = μ.support`. The subdifferential is the published
`StochasticProg.RecourseKKT.subdifferential` of the `EReal` function `x ↦ Q(x; ξ)` (Chapter 1,
Def. 3.2 for a finite function); "subdifferentiable at `x̂`" is nonemptiness of `∂ₓQ(x̂; ξ)`, asserted
at every `x̂`. The argmax set is the published `KallMayer.Recourse.DualOptimizers W q(ξ) (h(ξ) − T(ξ)x̂)`.
The standing assumption `ξ ∈ L²` of the section is not needed and not assumed. -/
theorem theorem_2_2 {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (hW : CompleteRecourse W)
    (hdual : ∀ ξ ∈ μ.support, ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q ξ) :
    ∀ ξ ∈ μ.support, ∀ xhat : Fin n₁ → ℝ,
      (subdifferential (fun x => PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x) xhat).Nonempty ∧
      subdifferential (fun x => PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x) xhat =
        {g | ∃ u ∈ DualOptimizers W (D.q ξ) (D.h ξ - D.T ξ *ᵥ xhat),
          g = -((D.T ξ).transpose *ᵥ u)} := by sorry

end KallMayerSLP.Recourse
