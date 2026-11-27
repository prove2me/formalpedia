-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_6
-- name    : IncentiveFinNet.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:33:28.247489+00:00
-- url     : https://prove2.me/theorems/d974abb5-0ce7-5da7-a707-d5db2819def4
-- title:
--   Theorem 6 — with separable frictions there is a unique stable point
-- statement:
--   Consider a network setting in which all agents share the covariance $\Sigma_i=\Sigma$ and all edges are allowed ($J_i=[n]$). For each agent $i$ let $F_i:\mathbb R^n\to\mathbb R$ be twice differentiable, and suppose there are strictly increasing functions $f_{ji}:\mathbb R\to\mathbb R$ such that for all $x\in\mathbb R^n$
--
--   $$
--   \nabla F_i(x) = \bigl(f_{1i}(x_1),\dots,f_{ni}(x_n)\bigr)^{\top}.
--   $$
--
--   Then there is exactly one pair $(W,P)$ that is a stable point for the utilities with friction (2),
--   $$
--   g_i(W,P) = w_i^{\top}(\mu_i - Pe_i) - \gamma_i\,w_i^{\top}\Sigma w_i - F_i(w_i).
--   $$
--
--   Frictions such as penalties on large contracts, imposed for instance by a regulator, therefore never destroy the existence or the uniqueness of the stable network when they are separable and convex.
--
--   Differences from the source:
--
--   - reading: "there exists a unique stable point" → there is exactly one pair (W, P) that is stable for the utilities (2) (StableF: Definitions 2–3 with (2) in place of (1)); reason: Theorem 6 is stated in §3.1, whose utility is (2)
--   - encoding: F_i twice differentiable with ∇F_i(x) = [f_1i(x_1), …, f_ni(x_n)]ᵀ → Differentiable ℝ (F i), Differentiable ℝ (fderiv ℝ (F i)), and fderiv ℝ (F i) x (e_j) = f j i (x j); reason: literal reading of twice differentiable (no continuity of the second derivative); the j-th partial derivative is the j-th gradient entry
--   - encoding: Σ_i = Σ and all edges allowed → ∀ i, S.Sig i = Σ and ∀ i, S.J i = univ on a general network setting; reason: Lean convention; same settings
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 6, p.19; utility (2), p.18; restated and proved in A.12, pp.46–47

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Supplement_StableF

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Theorem 6**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, §3.1, p.19 (restated in A.12,
p.46): "Consider a network setting where `Σ_i = Σ` and all edges are allowed. Suppose that for each
firm `i ∈ [n]`, the function `F_i : ℝⁿ → ℝ` is twice differentiable, and there exist strictly
increasing functions `f_ji : ℝ → ℝ` such that for all `x ∈ ℝⁿ`,
`∇F_i(x) = [f_1i(x_1), …, f_ni(x_n)]ᵀ`. Then, there exists a unique stable point."

The stable point is for the utilities (2) with friction `F_i` (`StableF`, p.18), and it is unique
as a pair `(W, P)`.

**Formalization Note**
* `Σ_i = Σ` is `∀ i, S.Sig i = Sig`; "all edges are allowed" is `J_i = [n]` (`Ψ_i = I_n`).
* "Twice differentiable" is `Differentiable ℝ (F i)` and `Differentiable ℝ (fderiv ℝ (F i))`
  (not `C²`); the gradient condition says that the `j`-th partial derivative of `F_i` at `x` is
  `f_ji(x_j)`. -/
theorem theorem_6 {n : ℕ} (S : NetworkSetting n) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hSig : ∀ i, S.Sig i = Sig) (hJ : ∀ i, S.J i = Finset.univ)
    (F : Fin n → (Fin n → ℝ) → ℝ) (f : Fin n → Fin n → ℝ → ℝ)
    (hF1 : ∀ i, Differentiable ℝ (F i)) (hF2 : ∀ i, Differentiable ℝ (fderiv ℝ (F i)))
    (hgrad : ∀ i x j, fderiv ℝ (F i) x (Pi.single j 1) = f j i (x j))
    (hf : ∀ j i, StrictMono (f j i)) :
    ∃! WP : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ, StableF S F WP.1 WP.2 := by sorry

end IncentiveFinNet.Supplement
