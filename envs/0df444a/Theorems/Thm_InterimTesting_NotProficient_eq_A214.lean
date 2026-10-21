-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_eq_A214
-- name    : InterimTesting.NotProficient.eq_A214
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:58.422526+00:00
-- url     : https://prove2.me/theorems/40cf0ea1-4c88-4ff5-a14e-e295a4623ed4
-- title:
--   (A214), p. A32 (PDF 58) — second steps of (A211)/(A212) compare iff µ0(B) ≤ µ; ℋ^I_1 ≤ ℋ2 ≤ ℋ^I_2; under (14) ℋ1 ≤ ℋ2 ≤ M_U
-- statement:
--   Suppose $B>0$. Then:
--
--   1. comparing the second steps of (A211) and (A212),
--   $$\mu\big(B(A\phi_{P|P}+B)+(1-\mu B)(A\phi_{P|N}+B)\big)\le\mu B\big((A+B)+(1-\mu B)\big)\iff\mu_0(B)\le\mu,\qquad\mu_0(B)=\frac1B-\frac{1-\phi_{P|P}}{\phi_{P|N}};$$
--   2. $\mathcal H^I_1(\mu)\le\mathcal H_2(\mu)\le\mathcal H^I_2(\mu)$;
--   3. if moreover (14) holds, $\mathcal H_1(\mu)\le\mathcal H_2(\mu)\le M_U$, so the budget ranges of (A211) are ordered.
--
--   Part 1 decides which assessment is better in the budget range where both curves are on their second step.
--
--   **Formalization Note** Part 3 is not printed as a separate claim; it is the well-ordering of the ranges in (A211), which the page uses.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A32 (PDF 58), (A214) and the sentence after it, proof of Proposition 1

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- (A214) and the orderings stated after it, p. A32: comparing the second steps of (A211) and
(A212) gives `μ0(B) ≤ μ`; `ℋ^I_1(μ) ≤ ℋ2(μ) ≤ ℋ^I_2(μ)`; and, under (14), the breakpoints of
(A211) are ordered, `ℋ1(μ) ≤ ℋ2(μ) ≤ M_U`. -/
theorem eq_A214 (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) :
    (θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
        ≤ θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B)) ↔ mu0 θ ≤ θ.μ) ∧
      HI1 θ ≤ H2 θ ∧ H2 θ ≤ HI2 θ ∧
      (Cond14 θ → H1 θ ≤ H2 θ ∧ H2 θ ≤ MU θ) := by sorry

end InterimTesting.NotProficient
