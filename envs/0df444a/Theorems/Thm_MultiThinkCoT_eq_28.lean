-- Prove2me | Theorems.Thm_MultiThinkCoT_eq_28
-- name    : MultiThinkCoT.eq_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:11.552209+00:00
-- url     : https://prove2.me/theorems/2cdf8550-380c-4ffe-a9d7-d240e50f6dcb
-- title:
--   Eq. (28) — $\mathrm{VCdim}(H_{\mathrm{boost}}(K))=O(K\,\mathrm{VCdim}\log(K\,\mathrm{VCdim}))$
-- statement:
--   There is a universal constant $c>0$ such that for every base class $\mathcal F$, generation length $T$, domain $\mathcal X$ and $K\in\mathbb N$ with $\mathrm{VCdim}(\mathcal F^{\mathrm{e2e}\text{-}T})=v<\infty$ (over $\mathcal X$), the class $H_{\mathrm{boost}}(K)$ of weighted majorities has finite VC dimension and
--
--   $$
--   \mathrm{VCdim}\big(H_{\mathrm{boost}}(K)\big)\ \le\ c\,K\,v\,\max\{1,\log(Kv)\}.
--   $$
--
--   This bound feeds Lemma F.4: the output of Algorithm 1 lies in $H_{\mathrm{boost}}(K)$ with $K=\lceil8\log(2m)\rceil$, and its capacity is what the sample size must beat.
--
--   **Formalization Note** Following the paper's convention for logarithmic factors in asymptotic upper bounds (p.16), the factor is $\max\{1,\log(Kv)\}$ (natural log); a plain logarithm would make the bound false at $Kv=1$.
--
--   Differences from the source:
--   - encoding: VCdim(H_boost(K)) = O(K·VCdim(F^{e2e-T}) log(K·VCdim(F^{e2e-T}))) → ∃ universal c > 0: VCdim(H_boost(K)) is a natural number n with n ≤ c K v max{1, log(Kv)} whenever VCdim(F^{e2e-T}) = v < ∞; reason: O(·) hides a universal constant and log u means max{1, log u} in asymptotic upper bounds (p.16)
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, eq. (28), p.56 (PDF p.56)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_e2eClass
import Definitions.Def_MultiThinkCoT_hboost

namespace MultiThinkCoT

/-- **Eq. (28)**, Appendix F, p.56 (PDF p.56).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

`VCdim(H_boost(K)) = O(K · VCdim(F^{e2e-T}) log(K · VCdim(F^{e2e-T})))`: there is a universal
`c > 0` such that for every base class `F`, generation length `T`, domain `X` and `K ∈ ℕ` with
`VCdim(F^{e2e-T}) = v < ∞`, the class `H_boost(K)` of (26) has finite VC dimension at most
`c · K · v · max{1, log(K v)}`.

**Formalization Note.** Following the paper's convention for asymptotic upper bounds (p.16), the
logarithmic factor is `max{1, log(Kv)}` (natural log); with a plain `log` the bound would fail at
`Kv = 1`. VC dimensions are over `X` (`UnderstandingML.vcDim`).
-/
theorem eq_28 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (K v : ℕ),
      UnderstandingML.vcDim (e2eClass F T X) = v →
      ∃ n : ℕ, UnderstandingML.vcDim (hboost F T X K) = n ∧
        (n : ℝ) ≤ c * K * v * max 1 (Real.log (K * v)) := by sorry

end MultiThinkCoT
