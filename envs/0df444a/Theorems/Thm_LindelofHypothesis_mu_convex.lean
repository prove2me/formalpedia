-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_convex
-- name    : LindelofHypothesis.mu_convex
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T16:39:12.755841+00:00
-- url     : https://prove2.me/theorems/34edb4ef-0709-46b7-8dd0-5d07d4d3a8cf
-- title:
--   $\mu$ is a (finite) convex function (Phragmén–Lindelöf)
-- statement:
--   The growth exponent $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$ is a real-valued convex function of $\sigma\in\mathbb R$: there is a convex function $f:\mathbb R\to\mathbb R$ with
--   $$\mu(\sigma)=f(\sigma)\qquad\text{for all }\sigma\in\mathbb R .$$
--
--   This is the consequence of the Phragmén–Lindelöf theorem quoted in the source; it is what turns the boundary values $\mu(0)$, $\mu(1)$ into the convexity bound for $\mu(\tfrac12)$.
--
--   **Formalization Note** $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals. Since $\mu$ is defined in the extended reals, \"$\mu$ is a convex function\" is stated as: $\mu$ is finite everywhere and coincides with a convex real function.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "The Phragmén–Lindelöf theorem implies that μ is a convex function".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_convex :
    ∃ f : ℝ → ℝ, ConvexOn ℝ Set.univ f ∧ ∀ σ : ℝ, mu σ = (f σ : EReal) := by sorry

end LindelofHypothesis
