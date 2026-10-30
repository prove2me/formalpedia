-- Prove2me | Theorems.Thm_OnlineCRS_Combine_fkg_active_set
-- name    : OnlineCRS.Combine.fkg_active_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:27:05.523498+00:00
-- url     : https://prove2.me/theorems/7264fe8d-6598-4948-9196-d6d4713ee6b4
-- title:
--   FKG (Harris) inequality for the active set $R(x)$
-- statement:
--   Let $x\in[0,1]^N$ and let $\mathcal A,\mathcal B\subseteq 2^N$ be down-closed families. Then
--   $$\Pr[R(x)\in\mathcal A]\cdot\Pr[R(x)\in\mathcal B]\ \le\ \Pr[R(x)\in\mathcal A\cap\mathcal B],$$
--   where $\Pr[R(x)\in\mathcal A]=\sum_{A\in\mathcal A}\prod_{e\in A}x_e\prod_{e\notin A}(1-x_e)$.
--
--   Decreasing events of a random set with independent elements are positively correlated. The proof of Lemma 2.11 applies this to the decreasing events $\chi_e(R,\mathcal F_{\pi^1,x},\cdot)$ and $\chi_e(R,\mathcal F_{\pi^2,x},\cdot)$.
--
--   Differences from the source:
--   - reading: 'by the FKG inequality' (no statement given) → the FKG (Harris) inequality for two down-closed families under the product law of R(x), x ∈ [0,1]^N; reason: this is the instance of the FKG inequality the step uses: the events are decreasing in R (by the monotonicity of χ_e in its first argument) and R(x) has independent coordinates
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, proof of Lemma 2.11 (unnumbered step 'by the FKG inequality'), p. 16

import Mathlib
import Definitions.Def_OnlineCRS_Combine_DownClosed
import Definitions.Def_OnlineCRS_Combine_activeProb

namespace OnlineCRS.Combine

/-- **FKG (Harris) inequality for the active set `R(x)`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, proof of Lemma 2.11, p. 16 (unnumbered): "Hence, if we let `R` be a random set distributed
like `R(x)`, then, by the FKG inequality: …"

For `x ∈ [0,1]^N` and down-closed families `𝒜, ℬ` of subsets of `N`,
`Pr[R(x) ∈ 𝒜] · Pr[R(x) ∈ ℬ] ≤ Pr[R(x) ∈ 𝒜 ∩ ℬ]`: decreasing events of the independent random
set `R(x)` are positively correlated.

**Formalization Note.** `Pr[R(x) ∈ 𝒜] = ∑_{A ∈ 𝒜} activeProb x A`. The paper invokes "the FKG
inequality" for the decreasing events `{χ_e(R, ·, ·)}`; this is that inequality for the law of
`R(x)`. -/
theorem fkg_active_set {N : Type*} [Fintype N] [DecidableEq N] {x : N → ℝ}
    (hx : x ∈ Set.Icc (0 : N → ℝ) 1) {𝒜 ℬ : Finset (Finset N)}
    (h𝒜 : DownClosed 𝒜) (hℬ : DownClosed ℬ) :
    (∑ A ∈ 𝒜, activeProb x A) * (∑ A ∈ ℬ, activeProb x A) ≤ ∑ A ∈ 𝒜 ∩ ℬ, activeProb x A := by sorry

end OnlineCRS.Combine
