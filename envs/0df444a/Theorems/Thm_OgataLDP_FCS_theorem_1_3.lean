-- Prove2me | Theorems.Thm_OgataLDP_FCS_theorem_1_3
-- name    : OgataLDP.FCS.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:41.69841+00:00
-- url     : https://prove2.me/theorems/3388ec22-0587-4834-add5-8816dbc9677f
-- title:
--   Theorem 1.3 — differentiable logarithmic moment generating function implies a good LDP
-- statement:
--   Let $\mu_n$, $n\ge1$, be probability measures on $\mathbb R$. Suppose the limit
--
--   $$f(\alpha)=\lim_{n\to\infty}\frac1n\log\int_{\mathbb R}e^{n\alpha x}\,d\mu_n(x)$$
--
--   exists as a finite real number for every $\alpha\in\mathbb R$, and $f$ is differentiable everywhere. Define $I(x)=\sup_{\alpha\in\mathbb R}\{\alpha x-f(\alpha)\}$. Then $I$ is a good rate function and $(\mu_n)$ satisfies the full large-deviation principle with rate $I$.
--
--   This is the Gärtner–Ellis result quoted by Ogata to pass from a differentiable pressure to the large-deviation bounds.
--
--   **Formalization Note** The exponential moment is a nonnegative lower integral, so infinite moments are not assigned a spurious zero. The rate uses an extended nonnegative supremum; the zero-parameter term equals zero for probability measures.
-- source:
--   Ogata, arXiv:0803.0113v1, pp. 4–5, Theorem 1.3

import Mathlib
import Definitions.Def_OgataLDP_FCS_Model

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OgataLDP.FCS

/-- Ogata, arXiv:0803.0113v1, pp. 4–5, Theorem 1.3 (Gärtner–Ellis). -/
theorem theorem_1_3 (mu : ℕ → Measure ℝ)
    (hmu : ∀ n, 0 < n → IsProbabilityMeasure (mu n)) (f : ℝ → ℝ)
    (hf : ∀ a : ℝ,
      Tendsto (fun n : ℕ => (1 / (n : EReal)) *
        ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp ((n : ℝ) * a * x)) ∂(mu n)))
        atTop (𝓝 (f a : EReal)))
    (hdiff : Differentiable ℝ f) :
    IsGoodRate (fun x : ℝ => ⨆ a : ℝ, ENNReal.ofReal (a * x - f a)) ∧
      SatisfiesLDP mu (fun x : ℝ => ⨆ a : ℝ, ENNReal.ofReal (a * x - f a)) := by sorry

end OgataLDP.FCS
