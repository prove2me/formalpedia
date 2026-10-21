-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A12
-- name    : InterimTesting.NotProficient.lemma_A12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:00.367893+00:00
-- url     : https://prove2.me/theorems/e74a7294-bff6-4004-aebb-a5ebda6fcc08
-- title:
--   Lemma A12, p. A30 (PDF 56) — there is µ1 with ℋ1(µ) ≤ ℋ^I_1(µ) iff µ ≥ µ1; if µ1 ≤ 1 then µ1 ≥ µ0(B)
-- statement:
--   Suppose $B>0$ and hold $A,B,\phi_{P|P},\phi_{P|N}$ fixed, letting the improvement potential factor $\mu$ vary in $(0,1)$. There exists $\mu_1$ such that, for all $\mu\in(0,1)$,
--   $$\mathcal H_1(\mu)\le\mathcal H^I_1(\mu)\iff\mu\ge\mu_1,$$
--   and if $\mu_1\le1$ then $\mu_1\ge\mu_0(B)=\frac1B-\frac{1-\phi_{P|P}}{\phi_{P|N}}$.
--
--   The threshold $\mu_1$ orders the two low-budget breakpoints of Proposition 1.
--
--   **Formalization Note** $\mathcal H_1$ and $\mathcal H^I_1$ at $\mu$ are evaluated at the parameter record with its `μ` field replaced; $\mu_0(B)$ does not involve $\mu$.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A30 (PDF 56), Lemma A12

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A12, p. A30: with all parameters but `μ` fixed, there is `μ1` such that
`ℋ1(μ) ≤ ℋ^I_1(μ)` exactly for `μ ≥ μ1` (`μ ∈ (0, 1)`), and if `μ1 ≤ 1` then `μ1 ≥ μ0(B)`
(`μ0(B)` does not depend on `μ`). -/
theorem lemma_A12 (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) :
    ∃ μ1 : ℝ,
      (∀ μ ∈ Set.Ioo (0 : ℝ) 1,
        (H1 { θ with μ := μ } ≤ HI1 { θ with μ := μ } ↔ μ1 ≤ μ)) ∧
      (μ1 ≤ 1 → mu0 θ ≤ μ1) := by sorry

end InterimTesting.NotProficient
