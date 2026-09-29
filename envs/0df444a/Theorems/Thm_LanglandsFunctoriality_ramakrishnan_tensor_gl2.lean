-- Prove2me | Theorems.Thm_LanglandsFunctoriality_ramakrishnan_tensor_gl2
-- name    : LanglandsFunctoriality.ramakrishnan_tensor_gl2
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:35:54.399878+00:00
-- url     : https://prove2.me/theorems/74f7d534-66ea-4cd2-93f7-0f91ae3323cf
-- title:
--   Example 5.5, $m=n=2$: the tensor product lift $GL(2)\times GL(2)\to GL(4)$
-- statement:
--   This is the case $m=n=2$ of Example 5.5 of the survey: functoriality for the tensor product
--   $L$-homomorphism $GL(2,\mathbb C)\times GL(2,\mathbb C)\to GL(4,\mathbb C)$.
--
--   Let $\pi$ and $\tau$ be cuspidal automorphic data of rank two, with Satake parameters
--   $\operatorname{diag}(\alpha_{p,1},\alpha_{p,2})$ and $\operatorname{diag}(\beta_{p,1},\beta_{p,2})$.
--   The tensor product lift $\pi\boxtimes\tau$ is the datum of rank four with Satake class
--
--   $$\operatorname{diag}\bigl(\alpha_{p,i}\beta_{p,j}\bigr)_{1\le i,j\le2}\subset GL(4,\mathbb C),$$
--
--   and the assertion is that some datum of rank four with these parameters outside a finite set of
--   primes is automorphic. Ramakrishnan established this case, using the converse theorem for $GL(4)$ of
--   Cogdell and Piatetski-Shapiro.
--
--   **Formalization Note.** The conclusion uses the weak notion of automorphy, which is the appropriate
--   one here: $\pi\boxtimes\pi$ is not cuspidal, and its $L$-function has a pole.
-- source:
--   J.-H. Yang, Langlands Functoriality Conjecture, arXiv:0808.0917 (2008), https://arxiv.org/abs/0808.0917, p. 20, Example 5.5 (tensor product lift), case m = n = 2

import Mathlib
import Definitions.Def_LanglandsFunctoriality_automorphic_data
import Definitions.Def_LanglandsFunctoriality_transfer

open Complex Polynomial

namespace LanglandsFunctoriality

theorem ramakrishnan_tensor_gl2 (π τ : LData 2) (hπ : IsCuspidalAutomorphic 2 π)
    (hτ : IsCuspidalAutomorphic 2 τ) :
    ∃ Pi : LData 4, IsAutomorphicL Pi ∧
      HasSatakeMultiset Pi fun p => tensorMultiset (π.satake p) (τ.satake p) := by sorry

end LanglandsFunctoriality
