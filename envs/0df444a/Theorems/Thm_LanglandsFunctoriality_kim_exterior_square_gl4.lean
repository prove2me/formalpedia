-- Prove2me | Theorems.Thm_LanglandsFunctoriality_kim_exterior_square_gl4
-- name    : LanglandsFunctoriality.kim_exterior_square_gl4
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:38:25.133197+00:00
-- url     : https://prove2.me/theorems/07e0e8f5-4275-4ec0-91b0-c0d5b5cce90e
-- title:
--   Example 5.7, $n=4$: the exterior square lift $\wedge^2 : GL(4)\to GL(6)$
-- statement:
--   This is the case $n=4$ of Example 5.7 of the survey: functoriality for the exterior square
--   $\wedge^2:GL(4,\mathbb C)\to GL(6,\mathbb C)$.
--
--   Let $\pi$ be a cuspidal automorphic datum of rank four with Satake class
--   $\operatorname{diag}(\alpha_{p,1},\dots,\alpha_{p,4})$. The exterior square lift $\wedge^2\pi$ is
--   the datum of rank six with Satake class
--
--   $$\operatorname{diag}\bigl(\alpha_{p,i}\alpha_{p,j}\bigr)_{1\le i<j\le4}\subset GL(6,\mathbb C),$$
--
--   and the assertion is that some datum of rank six with these parameters outside a finite set of
--   primes is automorphic. Kim established this case, the functorial lift from $GL(4)$ to $GL(6)$.
--
--   **Formalization Note.** At rank four the cuspidality hypothesis is genuinely recursive: besides the
--   functional equation for $\pi$ itself, it requires niceness of every Rankin–Selberg twist of $\pi$ by
--   a cuspidal automorphic datum of rank one or two.
-- source:
--   J.-H. Yang, Langlands Functoriality Conjecture, arXiv:0808.0917 (2008), https://arxiv.org/abs/0808.0917, p. 21, Example 5.7 (exterior square lift), case n = 4

import Mathlib
import Definitions.Def_LanglandsFunctoriality_automorphic_data
import Definitions.Def_LanglandsFunctoriality_transfer

open Complex Polynomial

namespace LanglandsFunctoriality

theorem kim_exterior_square_gl4 (π : LData 4) (hπ : IsCuspidalAutomorphic 4 π) :
    ∃ Pi : LData 6, IsAutomorphicL Pi ∧
      HasSatakeMultiset Pi fun p => extSquareMultiset (π.satake p) := by sorry

end LanglandsFunctoriality
