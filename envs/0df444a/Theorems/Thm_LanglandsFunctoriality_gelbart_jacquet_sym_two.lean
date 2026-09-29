-- Prove2me | Theorems.Thm_LanglandsFunctoriality_gelbart_jacquet_sym_two
-- name    : LanglandsFunctoriality.gelbart_jacquet_sym_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T16:24:52.415348+00:00
-- url     : https://prove2.me/theorems/3210cf8c-a5fe-4d1f-b949-55a7c82c115b
-- title:
--   Example 5.6, $m=2$: the Gelbart--Jacquet lift $\mathrm{Sym}^2 : GL(2)\to GL(3)$
-- statement:
--   This is the case $\mathrm{Sym}^{2}$ of Example 5.6 of the survey: functoriality for the
--   $L$-homomorphism $\mathrm{Sym}^{2}:GL(2,\mathbb C)\to GL(3,\mathbb C)$.
--
--   Let $\pi$ be a cuspidal automorphic datum of rank two, with Satake parameters
--   $c(\pi_p)=\operatorname{diag}(\alpha_p,\beta_p)$ at the prime $p$. The symmetric power lift
--   $\mathrm{Sym}^{2}(\pi)$ is the datum of rank $3$ whose Satake class at $p$ is
--
--   $$\operatorname{diag}\bigl(\alpha_p^{2},\,\alpha_p^{2-1}\beta_p,\,\dots,\,\beta_p^{2}
--   \bigr)\subset GL(3,\mathbb C).$$
--
--   The assertion is that some datum of rank $3$ with these Satake parameters outside a finite set
--   of primes is automorphic: its completed $L$-functions are meromorphic with at most finitely many
--   poles and satisfy the standard functional equation. Gelbart and Jacquet established this case in 1978, using the converse theorem on $GL(3)$.
--
--   **Formalization Note.** The Satake matching is stated as an equality of the local Euler polynomials
--   with the product over the multiset $\{\alpha^{2-i}\beta^{i}\}_{0\le i\le 2}$, so no
--   ordering of the parameters is imposed; it is required outside an unspecified finite set of primes.
--   The conclusion uses the weak (possibly non-cuspidal) notion of automorphy.
-- source:
--   J.-H. Yang, Langlands Functoriality Conjecture, arXiv:0808.0917 (2008), https://arxiv.org/abs/0808.0917, pp. 20-21, Example 5.6 (symmetric power lifts of GL(2))

import Mathlib
import Definitions.Def_LanglandsFunctoriality_automorphic_data
import Definitions.Def_LanglandsFunctoriality_transfer

open Complex Polynomial

namespace LanglandsFunctoriality

theorem gelbart_jacquet_sym_two (π : LData 2) (hπ : IsCuspidalAutomorphic 2 π) :
    ∃ Pi : LData 3, IsAutomorphicL Pi ∧
      HasSatakeMultiset Pi fun p => symMultiset 2 (π.satake p 0) (π.satake p 1) := by sorry

end LanglandsFunctoriality
