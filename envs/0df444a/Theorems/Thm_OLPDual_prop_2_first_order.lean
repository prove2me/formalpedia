-- Prove2me | Theorems.Thm_OLPDual_prop_2_first_order
-- name    : OLPDual.prop_2_first_order
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:27.523228+00:00
-- url     : https://prove2.me/theorems/1013622d-472b-4c03-900d-a29e1161d76c
-- title:
--   Proof of Proposition 2, display (20), p.32 — $\nabla f(p^*)\cdot p^*=0$ and $\nabla f(p^*)\ge 0$
-- statement:
--   Under Assumptions 1 and 2, at the optimal solution $p^*$ of (7),
--
--   $$
--   \nabla f(p^*)\cdot p^*=0,\qquad\nabla f(p^*)\ge 0,
--   $$
--
--   where $\cdot$ is the element-wise product and the inequality is entrywise. Consequently $\nabla f(p^*)^\top(p-p^*)\ge 0$ for every $p\ge 0$.
--
--   This is the complementary slackness of the stochastic program. It is used in the uniqueness part of Proposition 2 and to discard the first-order term in (30).
--
--   Differences from the source:
--   - generalization: (20) and ∇f(p*) ≥ 0 → adds the conjunct ∇f(p*)ᵀ(p − p*) ≥ 0 for every p ≥ 0; reason: the immediate consequence the paper uses on p.33 and for (30); the first two conjuncts are the printed claims
--   - reading: λ_min is the minimum eigenvalue of M = E[aaᵀ]; Ξ satisfies Assumptions 1–2 → Model fixes positive r̄, ā, d̲ < d̄, λ, μ, λ_min, and λ_min is any lower bound on that eigenvalue; reason: p.13 says the parameters do not depend on 𝒫; the eigenvalue itself is one admissible value of lamMin
--   - encoding: (r, a) ∼ 𝒫 and ℙ(· | a) → the law of (a, r) is Pa ⊗ₘ κ with a Markov kernel κ, and Assumption 2 (b) reads ∀ p ∈ Ω_p, ∀ᵐ a; reason: every law on ℝ^m × ℝ disintegrates so; the order (a, r) fits Measure.compProd
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), proof of Proposition 2, display (20), p.32; proof of (20) pp.32–33

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Proof of Proposition 2, display (20)**, Li–Ye, arXiv:1909.05499v5, p.32 (PDF 32):
`∇f(p*) · p* = 0` (element-wise product) and `∇f(p*) ≥ 0`.
**Formalization Note** The third conjunct, `∇f(p*)ᵀ(p − p*) ≥ 0` for every `p ≥ 0`, is the immediate
consequence the paper uses on p.33 and in (30), p.40. -/
theorem prop_2_first_order (Θ : Model) {m : ℕ} (d : E m) (Pa : Measure (E m))
    [IsProbabilityMeasure Pa] (κ : Kernel (E m) ℝ) [IsMarkovKernel κ] (pstar : E m)
    (hA1 : Assumption1 Θ d (Pa ⊗ₘ κ)) (hmin : IsOptimal (f d (Pa ⊗ₘ κ)) pstar)
    (hA2 : Assumption2 Θ d Pa κ pstar) :
    (∀ i, (gradf d (Pa ⊗ₘ κ) pstar) i * pstar i = 0) ∧
    (∀ i, 0 ≤ (gradf d (Pa ⊗ₘ κ) pstar) i) ∧
    ∀ p ∈ orthant m, 0 ≤ ⟪gradf d (Pa ⊗ₘ κ) pstar, p - pstar⟫ := by sorry

end OLPDual
