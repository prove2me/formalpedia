-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_theorem_2_4
-- name    : KallMayerSLP.Recourse.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:26.725194+00:00
-- url     : https://prove2.me/theorems/7c17b7ff-956b-4e06-9381-e9064cff2dc7
-- title:
--   Theorem 2.4 — Jensen lower bound for the expected recourse
-- statement:
--   Let $W\in\mathbb R^{m_2\times n_2}$ be fixed, let $T(\xi),h(\xi)$ be affine in $\xi$ as in (2.1), let the cost $q$ be deterministic, and let $\xi$ be an integrable random vector in $\mathbb R^r$ with distribution $\mathbb P_\xi$ and mean $\bar\xi=\mathbb E_\xi[\xi]$. Assume complete recourse (Assumption 2.1) and $\{u\mid W^{\mathsf T}u\le q\}\neq\emptyset$ (Assumption 2.2). Then for every $x\in\mathbb R^{n_1}$ the expected recourse $\mathcal Q(x)=\mathbb E_\xi[Q(x;T(\xi),h(\xi))]$ is a finite integral, $Q(x;T(\bar\xi),h(\bar\xi))$ is finite, and
--
--   $$
--   Q(x;T(\bar\xi),h(\bar\xi))\le\mathcal Q(x). \tag{2.14}
--   $$
--
--   The bound replaces the distribution by the one-point distribution at its mean; it is the starting point of the successive discrete approximation (bounding) methods of the chapter.
--
--   **Formalization Note** $\bar\xi$ is the Bochner integral $\int\xi\,d\mathbb P_\xi$ and $\mathcal Q$ the published `KallMayer.Recourse.ExpectedRecourse` with constant cost $q$ (the field `q0`). The conclusion asserts integrability of the recourse value, finiteness of the left-hand side, and the inequality between real numbers.
--
--   Differences from the source:
--   - encoding: probability space (Ω, ℱ, P) with ℱ = σ(ξ) and the induced distribution ℙ_ξ on ℝʳ → a probability measure μ = ℙ_ξ on `Fin r → ℝ` (canonical space, ξ = id); reason: the statement involves ξ only through ℙ_ξ; same instances
--   - encoding: T(ξ), h(ξ), q(ξ) affine in ξ by (2.1), W(ξ) ≡ W fixed → `RandomData` with fields T0, Tj, h0, hj, q0, qj and one fixed matrix W; reason: notation only
--   - encoding: recourse value Q(x; T(ξ), h(ξ), q(ξ)) as an inf with values ±∞ → the published `KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum (+∞ if infeasible, −∞ if unbounded); reason: the book's convention of p.200; same values
--   - encoding: 𝒬(x) = 𝔼_ξ[Q(x; T(ξ), h(ξ))] → the real part of Q(x; ξ) is integrable (with measurability), and 𝒬 = the published `KallMayer.Recourse.ExpectedRecourse` (Bochner integral of the real part); reason: under Assumption 2.1 and the ξ-independent Assumption 2.2 the recourse LP is primal and dual feasible for every ξ, so Q(x; ξ) is finite everywhere and its real part is Q itself
--   - encoding: the inequality (2.14) between extended values → Q(x; T(ξ̄), h(ξ̄)) ≠ ⊥, ≠ ⊤, and the inequality between its real part and 𝒬(x); reason: the left-hand side is finite for the same reason, so no infinite value is collapsed
--   - encoding: q(ξ) ≡ q deterministic → the field `D.q0` as constant cost; reason: same instances
--   - generalization: standing assumption ξ ∈ L² (p.199) → ξ integrable (`Integrable id μ`); reason: the text before the theorem (p.211) notes that Cor. 2.1 gives finiteness of 𝒬 for ξ ∈ L¹ in this deterministic-q setting; L² ⊂ L¹ on a probability space, so this specializes to the book's statement
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.4, p.211 (PDF 220); context q(ξ) ≡ q, p.210 (PDF 219)

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayer_Recourse_ExpectedRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData

open MeasureTheory
open KallMayer.Recourse (CompleteRecourse PointwiseRecourse ExpectedRecourse)
open Matrix

namespace KallMayerSLP.Recourse

/-- Theorem 2.4 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.4, p.211,
PDF 220): given the Assumptions 2.1 and 2.2, with `ξ̄ = 𝔼_ξ[ξ]`, the expected recourse
`𝒬(x) = 𝔼_ξ[Q(x; T(ξ), h(ξ))]` is bounded below due to `Q(x; T(ξ̄), h(ξ̄)) ≤ 𝒬(x)` (2.14).

Context (p.210): `q(ξ) ≡ q` deterministic, Assumption 2.2 reading `{u | Wᵀu ≤ q} ≠ ∅`.

**Formalization Note.** `μ = ℙ_ξ` on `ℝʳ`, `ξ̄ = ∫ ξ dμ`; the deterministic cost is `D.q0`. `ξ` is only
assumed integrable (`ξ ∈ L¹`, which Cor. 2.1 shows suffices, p.211) instead of `ξ ∈ L²`. The
conclusion asserts, for every `x`, that `Q(x; ξ)` has an integrable real part (so `𝒬(x)` is a genuine
finite integral), that `Q(x; T(ξ̄), h(ξ̄))` is finite, and the inequality (2.14) between the real
numbers. -/
theorem theorem_2_4 {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hξ : Integrable id μ)
    (hW : CompleteRecourse W)
    (hdual : ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q0)
    (x : Fin n₁ → ℝ) :
    Integrable (fun ξ => (PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x).toReal) μ ∧
    PointwiseRecourse W (D.T (∫ ξ, ξ ∂μ)) (D.h (∫ ξ, ξ ∂μ)) D.q0 x ≠ ⊥ ∧
    PointwiseRecourse W (D.T (∫ ξ, ξ ∂μ)) (D.h (∫ ξ, ξ ∂μ)) D.q0 x ≠ ⊤ ∧
    (PointwiseRecourse W (D.T (∫ ξ, ξ ∂μ)) (D.h (∫ ξ, ξ ∂μ)) D.q0 x).toReal ≤
      ExpectedRecourse μ W D.T D.h (fun _ => D.q0) x := by sorry

end KallMayerSLP.Recourse
