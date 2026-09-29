-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_trace_empty_shadow_matching
-- name    : FranklKupavskii2022.EMC.trace_empty_shadow_matching
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:17:33.93996+00:00
-- url     : https://prove2.me/theorems/4af86859-1679-40fa-8a46-a5185f176342
-- title:
--   Proposition 6: $\nu(\partial\mathcal F(\emptyset))\le s$
-- statement:
--   Let $n,k,s$ be positive integers with $n\ge k(s+1)$. If $\mathcal F\subseteq\binom{[n]}{k}$ is initial and $\nu(\mathcal F)\le s$, then
--
--   $$
--   \nu(\partial\mathcal F(\emptyset))\le s. \tag{12}
--   $$
--
--   Together with Lemma 5 this places the shadow of $\mathcal F(\emptyset)$ in the setting of Section 2.1, and in the appendix it lets the induction hypothesis on $k$ bound $|\partial\mathcal F(\emptyset)|$.
--
--   **Formalization Note** The family lives in $\binom{[n]}{k}$ as in the preceding Lemma 5; the Sect. 1 standing assumption is included.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Proposition 6, p. 4

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Proposition 6 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4): if `F` is initial and `ν(F) ≤ s`
then `ν(∂F(∅)) ≤ s` (12).

**Formalization Note.** As in Lemma 5 (the preceding statement on the page), `F ⊂ \binom{[n]}{k}`.
The Sect. 1 standing assumption "positive integers n, k, s satisfy n ≥ k(s + 1)" is kept as
`1 ≤ k`, `1 ≤ s`, `k * (s + 1) ≤ n`. -/
theorem trace_empty_shadow_matching (n k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : k * (s + 1) ≤ n)
    (F : Finset (Finset ℕ)) (hF : F ⊆ (Finset.Icc 1 n).powersetCard k) (hinit : IsInitial n k F)
    (hν : matchingNumber F ≤ s) :
    matchingNumber (∂ (trace s F ∅)) ≤ s := by sorry

end FranklKupavskii2022.EMC
