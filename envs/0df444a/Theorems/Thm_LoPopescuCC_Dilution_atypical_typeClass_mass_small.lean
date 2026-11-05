-- Prove2me | Theorems.Thm_LoPopescuCC_Dilution_atypical_typeClass_mass_small
-- name    : LoPopescuCC.Dilution.atypical_typeClass_mass_small
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:46.054771+00:00
-- url     : https://prove2.me/theorems/76aaee12-fa5c-411b-80e0-2fb290b17b71
-- title:
--   Proof of the Theorem, p. 5 — the atypical set is small
-- statement:
--   Let $p$ be a probability vector on $k$ letters with Shannon entropy $H(p)=-\sum_ip_i\log_2p_i$. For every $\varepsilon>0$ there is $C>0$ such that for every $N$,
--
--   $$
--   \sum_{x\ \text{atypical}}\ \prod_{j=1}^{N}p_{x_j}<\varepsilon,
--   $$
--
--   where a string $x\in\{0,\dots,k-1\}^N$ is atypical if the size $|T(x)|$ of its type class satisfies $\big|\log_2|T(x)|-NH(p)\big|>C\sqrt N$.
--
--   When $p=(\lambda_i)$ is the squared Schmidt spectrum of $\psi$, the left side is the squared norm of the projection of $\psi^N$ onto the atypical terms of its Schmidt decomposition, and $H(p)=S(\psi)$. This is why the atypical terms can be moved into the error $u_2$.
--
--   Differences from the source:
--   - generalization: two-term ψ, atypical values of k, log C(N,k) → any probability vector on k letters, atypical strings, log₂ of the type class size; reason: the page's proof is stated as general and illustrated on two terms; k = 2 gives the page's claim
--   - reading: the norm of the projection on the atypical terms is very small, with the window's coefficient depending on ε → ∀ ε > 0 ∃ C > 0 ∀ N, the sum of the squared norms of the atypical terms is below ε; reason: squared norm below ε for all ε is the same claim as norm small; the page says the coefficient depends on ε, and all N is stronger than N large
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Proof of the Theorem, p. 5

import Mathlib
import Definitions.Def_FuchsVdGraaf_entropy
import Definitions.Def_LoPopescuCC_Dilution_typeClassCard

namespace LoPopescuCC.Dilution

/-- **The atypical set is small** (Lo, Popescu, arXiv:quant-ph/9902045v2, Proof of the Theorem,
p. 5: "It is well-known that, compared to the measure of the typical set, the overall measure of
the atypical set is very small"). Let `p` be a probability vector on `k` letters with Shannon
entropy `H(p)` in bits. For every `ε > 0` there is `C > 0` such that, for every `N`, the strings `x`
whose type class size lies outside `2^{N H(p) ± C√N}` have total `p^N`-probability below `ε`.

**Formalization Note** When `p` is the spectrum `(λ_i)` of `ψ`, the sum is the squared norm of the
projection of `ψ^N` on the atypical Schmidt terms, and `H(p) = S(ψ)`. The window constant `C` depends
on `ε`, as the page says. The statement holds for all `N`: small `N` are absorbed into `C`.
`typeClassCard x ≥ 1`, so the logarithm is never at a junk value. -/
theorem atypical_typeClass_mass_small {k : ℕ} (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (∑ x : Fin N → Fin k, if C * Real.sqrt N < |Real.logb 2 (typeClassCard x) - N * FuchsVdGraaf.entropy p| then ∏ j, p (x j) else 0) < ε := by sorry

end LoPopescuCC.Dilution
