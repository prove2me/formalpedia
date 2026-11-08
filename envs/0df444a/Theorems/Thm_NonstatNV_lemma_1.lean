-- Prove2me | Theorems.Thm_NonstatNV_lemma_1
-- name    : NonstatNV.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T14:04:25.519488+00:00
-- url     : https://prove2.me/theorems/74e8ab2b-49d9-4939-8a60-e5b735763138
-- title:
--   Lemma 1 — an estimation error $|\mu_1-\mu_2|$ costs at most $2\ell|\mu_1-\mu_2|$
-- statement:
--   Consider a Nonstationary Newsvendor model satisfying the standing assumptions and Assumption 2 with constant $\ell$. Fix costs $b\in[0,b_{\max}]$ and $h\in[0,h_{\max}]$ and write $C(\mu,q)=C(\mu,b,h,q)$. Let $\mu_1,\mu_2\in[\mu_{\min},\mu_{\max}]$ and let $q_1^*\in\arg\min_{q\in Q}C(\mu_1,q)$, $q_2^*\in\arg\min_{q\in Q}C(\mu_2,q)$. Then
--
--   $$
--   C(\mu_1,q_2^*)-C(\mu_1,q_1^*)\le 2\ell\,|\mu_1-\mu_2| .
--   $$
--
--   Ordering optimally for a wrong mean thus costs at most linearly in the error of the mean. Every regret bound of the paper passes through this lemma.
--
--   Differences from the source:
--   - encoding: q* ∈ argmin_{q∈Q} C(μ, q) → q ∈ Q and C(μ, q) ≤ C(μ, q') for every q' ∈ Q; reason: definition of argmin; no instance changes
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Lemma 1, p.11 (proof p.34)

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost

open MeasureTheory

namespace NonstatNV

/-- **Lemma 1** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.11; proof p.34). Fix `b ∈ [0, bmax]`, `h ∈ [0, hmax]`. For
`μ₁, μ₂ ∈ [μmin, μmax]`, let `q₁ ∈ argmin_{q∈Q} C(μ₁, q)` and `q₂ ∈ argmin_{q∈Q} C(μ₂, q)`. Then
`C(μ₁, q₂) − C(μ₁, q₁) ≤ 2ℓ|μ₁ − μ₂|`, where `ℓ` is the Lipschitz constant of Assumption 2.

**Formalization Note** "`q ∈ argmin`" is the pair of hypotheses `q ∈ Q` and `C(μ, q) ≤ C(μ, q')`
for all `q' ∈ Q`. -/
theorem lemma_1 (M : Model) (ℓ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ)
    (b h : ℝ) (hb : b ∈ Set.Icc 0 M.bmax) (hh : h ∈ Set.Icc 0 M.hmax)
    (μ₁ μ₂ : ℝ) (hμ₁ : μ₁ ∈ Set.Icc M.μmin M.μmax) (hμ₂ : μ₂ ∈ Set.Icc M.μmin M.μmax)
    (q₁ q₂ : ℝ) (hq₁ : q₁ ∈ M.Q) (hq₁min : ∀ q ∈ M.Q, M.cost μ₁ b h q₁ ≤ M.cost μ₁ b h q)
    (hq₂ : q₂ ∈ M.Q) (hq₂min : ∀ q ∈ M.Q, M.cost μ₂ b h q₂ ≤ M.cost μ₂ b h q) :
    M.cost μ₁ b h q₂ - M.cost μ₁ b h q₁ ≤ 2 * ℓ * |μ₁ - μ₂| := by sorry

end NonstatNV
