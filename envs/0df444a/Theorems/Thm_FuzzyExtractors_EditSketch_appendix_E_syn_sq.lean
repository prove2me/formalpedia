-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_appendix_E_syn_sq
-- name    : FuzzyExtractors.EditSketch.appendix_E_syn_sq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:54.982246+00:00
-- url     : https://prove2.me/theorems/dc2db6b7-81cb-4a1b-ada1-30b9b1dac19d
-- title:
--   Appendix E — in characteristic 2 the even syndromes are squares: $s_{2i}(w) = s_i(w)^2$
-- statement:
--   Let $K$ be a finite field of characteristic $2$ and let $w \subseteq K^*$ be the support of a binary word. Write $s_i(w) = \sum_{x \in w} x^i$ for its $i$-th power-sum syndrome. Then for every $i \ge 0$
--   $$s_{2i}(w) = s_i(w)^2 .$$
--
--   This is the case $q = 2$ of the redundancy observed in Appendix E, $c(\alpha^i)^q = c(\alpha^{iq})$: since the coefficients of a binary word satisfy $c_x^2 = c_x$ and squaring is additive in characteristic $2$, the even-indexed syndromes are determined by the odd-indexed ones. This is why PinSketch (Construction 6) publishes only $s_1, s_3, \dots, s_{2t-1}$.
--
--   **Formalization Note.** The paper states the identity for general $q$ and a general word $(c_x) \in GF(q)^n$; only the binary case, with the word given by its support, is stated here. The field $GF(2^\mu)$ is any finite field of characteristic $2$.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Appendix E, p. 43 ("we have c(α^i)^q = Σ_{x≠0} c_x^q x^{iq} = c(α^{iq})")

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem appendix_E_syn_sq {K : Type} [Field K] [Fintype K] [CharP K 2]
    (w : Finset Kˣ) (i : ℕ) :
    syn (2 * i) w = syn i w ^ 2 := by sorry

end FuzzyExtractors.EditSketch
