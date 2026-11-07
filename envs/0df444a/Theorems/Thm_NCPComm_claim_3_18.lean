-- Prove2me | Theorems.Thm_NCPComm_claim_3_18
-- name    : NCPComm.claim_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:38.022823+00:00
-- url     : https://prove2.me/theorems/52c80ad0-7be4-434e-9cde-02b1011d900f
-- title:
--   Claim 3.18 — comparison and rounding of normal variables
-- statement:
--   Let $Z_b\sim\mathcal N(\mu_b,\sigma_b^2)$ with $\sigma_b>0$. There is an absolute constant $C$ with
--   $$
--   \delta_{\mathrm{TV}}(Z_0,Z_1)\le C\,\frac{|\mu_0-\mu_1|+|\sigma_0-\sigma_1|}{\min\{\sigma_0,\sigma_1\}},
--   $$
--   and for every integer $r$,
--   $$
--   \delta_{\mathrm{TV}}(\lceil Z_0\rceil+r,\lceil Z_1\rceil)\le\delta_{\mathrm{TV}}(Z_0+r,Z_1).
--   $$
--
--   **Formalization Note** Distances are the published `MarkovChainCLT.tvDist`, $\sup_A|\mu(A)-\nu(A)|$, on $\mathbb R$ and on $\mathbb Z$.
--
--   Differences from the source:
--   - reading: "C" with no quantifier on the page → C absolute, before all parameters; reason: the page's proof integrates derivatives of the normal density and gives an absolute constant; this is the stronger reading
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 3.18, p.18

import Mathlib
import Definitions.Def_TotalVariationDist

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 3.18 (Comparison and rounding of normal variables), p.18** (Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).
For `Z_b ∼ N(μ_b, σ_b²)` with `σ_b > 0`, `δ_TV(Z₀, Z₁) ≤ C(|μ₀-μ₁| + |σ₀-σ₁|)/min{σ₀, σ₁}` with an
absolute `C`, and `δ_TV(⌈Z₀⌉ + r, ⌈Z₁⌉) ≤ δ_TV(Z₀ + r, Z₁)` for every integer `r`.

**Formalization Note** The constant is placed before the parameters, since the page's proof gives an
absolute constant. `MarkovChainCLT.tvDist` is the published `sup_A |μ(A) - ν(A)|`. -/
theorem claim_3_18 :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ₀ μ₁ σ₀ σ₁ : ℝ), 0 < σ₀ → 0 < σ₁ →
      let Z₀ := ProbabilityTheory.gaussianReal μ₀ (Real.toNNReal (σ₀ ^ 2))
      let Z₁ := ProbabilityTheory.gaussianReal μ₁ (Real.toNNReal (σ₁ ^ 2))
      MarkovChainCLT.tvDist Z₀ Z₁ ≤ C * (|μ₀ - μ₁| + |σ₀ - σ₁|) / min σ₀ σ₁ ∧
      ∀ r : ℤ,
        MarkovChainCLT.tvDist (Z₀.map fun z : ℝ => ⌈z⌉ + r) (Z₁.map fun z : ℝ => ⌈z⌉)
          ≤ MarkovChainCLT.tvDist (Z₀.map fun z : ℝ => z + (r : ℝ)) Z₁ := by sorry

end NCPComm
