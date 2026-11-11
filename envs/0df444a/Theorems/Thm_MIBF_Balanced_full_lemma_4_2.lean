-- Prove2me | Theorems.Thm_MIBF_Balanced_full_lemma_4_2
-- name    : MIBF.Balanced.full_lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:59:19.381241+00:00
-- url     : https://prove2.me/theorems/6a02a2ca-a8f1-4a18-bfcd-76846e42e53d
-- title:
--   [Full] Lemma 4.2 — global entropy rearrangement: $G(a,c,e,f)\ge G(a,c,f,e)$ on $R_S$ when $e>f$
-- statement:
--   Bits throughout; $S=10^{-4}$ and
--   $$R_S=\Bigl\{(a,c,e,f):\ 0\le a\le c\le\tfrac12,\ a+c\ge S,\ 0<e\le H(a),\ 0<f\le H(c)\Bigr\},$$
--   where $G(a,c,e,f)$ is the pure gap at the tuple $(\mu_u,\mu_w,e_u,e_w)=(a,c,e,f)$. Then:
--   1. for every $(a,c,e,f)\in R_S$ with $e>f$,
--   $$G(a,c,e,f)\ \ge\ G(a,c,f,e);$$
--   2. consequently, if $G(a,c,e,f)<0$ for some $(a,c,e,f)\in R_S$, then $G<0$ at some point of $R_S$ in the chamber $e\le f$.
--
--   Putting the smaller entropy on the smaller mean never increases the pure gap, so the pure-gap inequality need only be proved for ordered entropies.
--
--   Differences from the source:
--   - reading: "every negative positive-entropy value has a negative representative in the chamber $e\le f$" → for every point of $R_S$ with $G<0$ there is a point of $R_S$ with $e\le f$ and $G<0$; reason: the sentence concerns the values on $R_S$ just compared.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 29 (PDF 51), Lemma 4.2 and the definition of R_S

import Mathlib
import Definitions.Def_MIBF_Balanced_PureGap

namespace MIBF.Balanced
theorem full_lemma_4_2 :
    (∀ a c e f : ℝ, InRS a c e f → f < e → pureGap a c f e ≤ pureGap a c e f) ∧
      (∀ a c e f : ℝ, InRS a c e f → pureGap a c e f < 0 →
        ∃ a' c' e' f' : ℝ, InRS a' c' e' f' ∧ e' ≤ f' ∧ pureGap a' c' e' f' < 0) := by sorry
end MIBF.Balanced
