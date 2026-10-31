-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_proposition_2_1
-- name    : KallMayerSLP.Recourse.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:30.44446+00:00
-- url     : https://prove2.me/theorems/49e5443c-4337-405b-ba87-8c0e7db4cc62
-- title:
--   Proposition 2.1 — with deterministic costs the recourse function is convex in $\xi$
-- statement:
--   Let $W\in\mathbb R^{m_2\times n_2}$ be fixed, let $T(\xi),h(\xi)$ be affine in $\xi\in\mathbb R^r$ as in (2.1), and let the second-stage cost be deterministic, $q(\xi)\equiv q$. Write
--
--   $$
--   Q(x;T(\xi),h(\xi))=\min\{q^{\mathsf T}y\mid Wy=h(\xi)-T(\xi)x,\ y\ge 0\}.
--   $$
--
--   Assume complete recourse (Assumption 2.1) and Assumption 2.2 in the form $\{u\mid W^{\mathsf T}u\le q\}\neq\emptyset$. Then for every $x\in\mathbb R^{n_1}$, $Q(x;T(\xi),h(\xi))$ is finite for every $\xi\in\mathbb R^r$, and
--
--   $$
--   \xi\ \longmapsto\ Q(x;T(\xi),h(\xi))\quad\text{is a convex function on }\mathbb R^r .
--   $$
--
--   Convexity in the random vector is what makes Jensen's inequality available, giving the lower bound of Theorem 2.4.
--
--   **Formalization Note** The deterministic cost is the field `q0` of the data structure; convexity is for the real part of the `EReal` recourse value, whose finiteness is part of the conclusion.
--
--   Differences from the source:
--   - encoding: T(ξ), h(ξ), q(ξ) affine in ξ by (2.1), W(ξ) ≡ W fixed → `RandomData` with fields T0, Tj, h0, hj, q0, qj and one fixed matrix W; reason: notation only
--   - encoding: recourse value Q(x; T(ξ), h(ξ), q(ξ)) as an inf with values ±∞ → the published `KallMayer.Recourse.PointwiseRecourse`, an `EReal` infimum (+∞ if infeasible, −∞ if unbounded); reason: the book's convention of p.200; same values
--   - encoding: Q(·; ξ) as a real function → `EReal.toReal` of the recourse value, with its finiteness asserted in the same statement; reason: no infinite value is collapsed
--   - encoding: q(ξ) ≡ q deterministic → the field `D.q0` is the cost of the recourse LP; `D.qj` is not used; reason: same instances
--   - reading: 'a convex function in ξ' (no domain given) → convex on all of ℝʳ, with Q finite there; reason: the proof uses only that the right-hand side is affine in ξ, for every ξ ∈ ℝʳ; with q deterministic Assumption 2.2 does not depend on ξ
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Proposition 2.1, p.210 (PDF 219)

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData

open KallMayer.Recourse (CompleteRecourse PointwiseRecourse)
open Matrix

namespace KallMayerSLP.Recourse

/-- Proposition 2.1 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Proposition 2.1,
p.210, PDF 219): assume that `q(ξ) ≡ q`, i.e. `q(·)` is deterministic. Given the Assumptions 2.1 and
2.2 (the latter one now reading as `{u | Wᵀu ≤ q} ≠ ∅`), `Q(x; T(·), h(·))` is a convex function in
`ξ` for any `x ∈ ℝ^{n₁}`.

**Formalization Note.** The deterministic cost is the field `D.q0` (the coefficients `D.qj` are not
used), so `Q(x; T(ξ), h(ξ)) = PointwiseRecourse W (T(ξ)) (h(ξ)) q x`. Convexity is stated for the real
function `ξ ↦ Q(x; ξ)` on all of `ℝʳ`, together with finiteness of `Q(x; ξ)` for every `ξ`, so that
taking the real part collapses no infinite value. -/
theorem proposition_2_1 {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ)
    (D : RandomData m₂ n₁ n₂ r)
    (hW : CompleteRecourse W)
    (hdual : ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q0)
    (x : Fin n₁ → ℝ) :
    (∀ ξ : Fin r → ℝ, PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x ≠ ⊥ ∧
      PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x ≠ ⊤) ∧
    ConvexOn ℝ Set.univ (fun ξ : Fin r → ℝ => (PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x).toReal) := by sorry

end KallMayerSLP.Recourse
