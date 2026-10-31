-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_theorem_2_1
-- name    : KallMayerSLP.Recourse.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:25.916891+00:00
-- url     : https://prove2.me/theorems/2bb19c34-f9ec-47f3-9408-357aefcc1d7f
-- title:
--   Theorem 2.1 — the recourse function is finite, convex and Lipschitz in $x$
-- statement:
--   Throughout, $\xi$ is a random vector in $\mathbb R^r$ with distribution $\mathbb P_\xi$ and support $\Xi=\operatorname{supp}\mathbb P_\xi$ (the smallest closed set of probability one); the second-stage data $T(\xi),h(\xi),q(\xi)$ are affine in $\xi$ as in (2.1), and the recourse matrix $W\in\mathbb R^{m_2\times n_2}$ is fixed. The **recourse function** is the optimal value of the second-stage LP (2.9),
--
--   $$
--   Q(x;T(\xi),h(\xi),q(\xi))=\min\{q^{\mathsf T}(\xi)y \mid Wy=h(\xi)-T(\xi)x,\ y\ge 0\},
--   $$
--
--   with value $+\infty$ when the LP is infeasible and $-\infty$ when it is unbounded. **Assumption 2.1** (complete fixed recourse, (2.6)): $\{z\mid z=Wy,\ y\ge 0\}=\mathbb R^{m_2}$. **Assumption 2.2** ((2.8)): $\{u\mid W^{\mathsf T}u\le q(\xi)\}\neq\emptyset$ for every $\xi\in\Xi$.
--
--   Assume Assumptions 2.1 and 2.2 and the standing assumption $\xi\in L^2$ (p.199). Then:
--
--   1. $Q(x;T(\xi),h(\xi),q(\xi))$ is finite for every $x\in\mathbb R^{n_1}$ and every $\xi\in\Xi$;
--   2. for every $\xi\in\Xi$, $x\mapsto Q(x;T(\xi),h(\xi),q(\xi))$ is convex on $\mathbb R^{n_1}$;
--   3. there is an integrable function $D(\xi)\in L^1(\mathbb P_\xi)$ such that for every $\xi\in\Xi$ and all $x^{(1)},x^{(2)}\in\mathbb R^{n_1}$
--
--   $$
--   \bigl|Q(x^{(1)};T(\xi),h(\xi),q(\xi))-Q(x^{(2)};T(\xi),h(\xi),q(\xi))\bigr|\le D(\xi)\,\|x^{(1)}-x^{(2)}\| .
--   $$
--
--   This is the scenario-wise regularity that Theorem 2.3 integrates to obtain the properties of the expected recourse.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm. Convexity and the Lipschitz bound are stated for the real part of the `EReal` recourse value, which by clause 1 is the value itself.
--
--   Differences from the source:
--   - encoding: probability space (Ω, ℱ, P) with ℱ = σ(ξ) and the induced distribution ℙ_ξ on ℝʳ → a probability measure μ = ℙ_ξ on `Fin r → ℝ` (canonical space, ξ = id); reason: the statement involves ξ only through ℙ_ξ; same instances
--   - encoding: Ξ = supp ℙ_ξ, the smallest closed set with ℙ_ξ(Ξ) = 1 → `μ.support` (Mathlib's support: points all of whose neighbourhoods have positive measure); reason: the two sets coincide in ℝʳ
--   - encoding: T(ξ), h(ξ), q(ξ) affine in ξ by (2.1), W(ξ) ≡ W fixed → `RandomData` with fields T0, Tj, h0, hj, q0, qj and one fixed matrix W; reason: notation only
--   - encoding: recourse value Q(x; T(ξ), h(ξ), q(ξ)) as an inf with values ±∞ → the published `KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum (+∞ if infeasible, −∞ if unbounded); reason: the book's convention of p.200; same values
--   - encoding: Q(·; ξ) as a real function → `EReal.toReal` of the recourse value, with its finiteness asserted in the same statement; reason: no infinite value is collapsed
--   - encoding: the norm ‖x⁽¹⁾ − x⁽²⁾‖ → the Euclidean norm `‖WithLp.toLp 2 (x₁ - x₂)‖`; reason: the book's ‖·‖ on ℝ^{n₁}
--   - generalization: clause a) for x ∈ B₁ = {x | Ax = b, x ≥ 0} → every x ∈ ℝ^{n₁}; reason: Assumption 2.1 makes the second-stage LP feasible for every x (proof of a)); B₁ ⊂ ℝ^{n₁}, so the statement specializes to the book's
--   - reading: b) 'convex in x', c) 'Lipschitz continuous in x' (no domain given) → on all of ℝ^{n₁}; reason: the proof of c) takes 'any two x⁽¹⁾ ≠ x⁽²⁾'; the function is defined and finite on ℝ^{n₁}
--   - encoding: 'Lipschitz constant D(ξ) ∈ L¹' → ∃ D : ℝʳ → ℝ, `Integrable D μ`, with the Lipschitz inequality for every ξ ∈ Ξ; reason: same content
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.1, p.205 (PDF 214)

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData

open MeasureTheory
open KallMayer.Recourse (CompleteRecourse PointwiseRecourse)
open Matrix

namespace KallMayerSLP.Recourse

/-- Theorem 2.1 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.1, p.205,
PDF 214): let Assumptions 2.1 and 2.2 be satisfied. Then the recourse function
`Q(x; T(ξ), h(ξ), q(ξ))` is
a) finitely valued `∀ x ∈ B₁, ξ ∈ Ξ`,
b) convex in `x` `∀ ξ ∈ Ξ`, and
c) Lipschitz continuous in `x` `∀ ξ ∈ Ξ` with a Lipschitz constant `D(ξ) ∈ L¹`.

**Formalization Note.** `μ = ℙ_ξ` on `ℝʳ`, `Ξ = μ.support`, `ξ ∈ L²` (the standing assumption of
p.199, needed for `D ∈ L¹`). Clause a) is stated for every `x ∈ ℝ^{n₁}` (the proof uses only primal
feasibility from Assumption 2.1, which holds for every `x`); `B₁ ⊂ ℝ^{n₁}`, so this contains the
book's clause. Clauses b) and c) concern the real function `x ↦ Q(x; ξ)`, which is the `toReal` of
the `EReal` recourse value; by a) no infinite value is collapsed. The norm in c) is the Euclidean
norm `‖x⁽¹⁾ − x⁽²⁾‖` of `ℝ^{n₁}` (`WithLp.toLp 2`). -/
theorem theorem_2_1 {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hξ : MemLp id 2 μ)
    (hW : CompleteRecourse W)
    (hdual : ∀ ξ ∈ μ.support, ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q ξ) :
    (∀ x : Fin n₁ → ℝ, ∀ ξ ∈ μ.support,
      PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊥ ∧
        PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊤) ∧
    (∀ ξ ∈ μ.support,
      ConvexOn ℝ Set.univ (fun x : Fin n₁ → ℝ => (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal)) ∧
    (∃ Dξ : (Fin r → ℝ) → ℝ, Integrable Dξ μ ∧
      ∀ ξ ∈ μ.support, ∀ x₁ x₂ : Fin n₁ → ℝ,
        |(PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x₁).toReal -
            (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x₂).toReal| ≤
          Dξ ξ * ‖WithLp.toLp 2 (x₁ - x₂)‖) := by sorry

end KallMayerSLP.Recourse
