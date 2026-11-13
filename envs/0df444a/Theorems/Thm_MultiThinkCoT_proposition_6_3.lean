-- Prove2me | Theorems.Thm_MultiThinkCoT_proposition_6_3
-- name    : MultiThinkCoT.proposition_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:54.159821+00:00
-- url     : https://prove2.me/theorems/2fb4bb84-252a-4997-9045-28a0c8e93de3
-- title:
--   Proposition 6.3, second display — $\mathrm{VCdim}(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F))=O(\mathrm{VCdim}(\mathcal F)\log T)$
-- statement:
--   There is a universal constant $c>0$ such that for every base class $\mathcal F$, thinking length $T$ and domain $\mathcal X$: if $\mathrm{VCdim}(\mathcal F)$, taken over the domain $\mathcal X\times\{0,1\}^{\le T-1}$, is $p<\infty$, then the CoT loss class has finite VC dimension and
--
--   $$
--   \mathrm{VCdim}\big(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F)\big)\ \le\ c\,p\,\max\{1,\log T\}.
--   $$
--
--   Through Lemma F.2 this bounds the per-source budget of Algorithm 1 in the relaxed protocol by $O(\mathrm{VCdim}(\mathcal F)\log T)$.
--
--   **Formalization Note** Only the second display of Proposition 6.3 is stated; the first display, $\mathrm{VCdim}(\mathcal F^{\mathrm{e2e}\text{-}T})\le O(T\cdot\mathrm{VCdim}(\mathcal F))$, is a separate claim that Theorem 7 does not use. The logarithmic factor is $\max\{1,\log T\}$ (natural log), per the paper's convention (p.16).
--
--   Differences from the source:
--   - encoding: VCdim(L^{CoT-T}(F)) = O(VCdim(F) log T) → ∃ universal c > 0: VCdim(L^{CoT-T}(F)) is a natural number w ≤ c p max{1, log T} whenever VCdim(F) over X × {0,1}^{≤T−1} is p < ∞; reason: O(·) is an upper bound with a universal constant; log u means max{1, log u} (p.16)
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §6.2, Proposition 6.3 (second display), p.18 (PDF p.18)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_cotLossClass
import Definitions.Def_MultiThinkCoT_prefixClass

namespace MultiThinkCoT

/-- **Proposition 6.3 (Theorems B.1, B.5 [JVB+25])**, second display, p.18 (PDF p.18).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

`VCdim(L^{CoT-T}(F)) = O(VCdim(F) log T)`, where `VCdim(F)` is taken over the domain
`X × {0,1}^{≤T−1}`: there is a universal `c > 0` such that for every `F`, `T` and `X` with
`VCdim(F)` over `X × {0,1}^{≤T−1}` equal to `p < ∞`, the CoT loss class (10) has finite VC
dimension at most `c · p · max{1, log T}`.

**Formalization Note.** Only the second display of Proposition 6.3 is stated (the first is not
used by Theorem 7). `O(·)` is an upper bound with a universal constant; the logarithmic factor is
`max{1, log T}` (natural log), the paper's convention for asymptotic upper bounds (p.16), without
which the bound fails at `T = 1`. `(x, p) ∈ X × {0,1}^{≤T−1}` acts as the string `[x, p]`.
-/
theorem proposition_6_3 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (p : ℕ),
      UnderstandingML.vcDim (prefixClass F T X) = p →
      ∃ w : ℕ, UnderstandingML.vcDim (cotLossClass F T X) = w ∧
        (w : ℝ) ≤ c * p * max 1 (Real.log T) := by sorry

end MultiThinkCoT
