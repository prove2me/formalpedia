-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_observation_4_2a
-- name    : GGHRSW.ColoredMatrix.observation_4_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:23.192781+00:00
-- url     : https://prove2.me/theorems/a782ee9b-3bd6-4c27-844b-be9be736d614
-- title:
--   §4.2, observation (a), p. 17 — if BP(χ) = 1 then F_χ(RND_p(BP)) = 0 (for every sample)
-- statement:
--   Let $p$ be a prime, $BP$ a length-$n$ branching program over $\ell$ input bits, and $\mathcal{RND}_p(BP)$ its randomized version (§4.1). For an input $\chi\in\{0,1\}^\ell$ consider the multilinear form
--   $$F_\chi(\mathcal{RND}_p(BP)) = \tilde{\mathbf s}\Big(\prod_i \tilde D_{i,\chi_{\mathsf{inp}(i)}}\Big)\tilde{\mathbf t} - \tilde{\mathbf s}'\Big(\prod_i \tilde D'_{i,\chi_{\mathsf{inp}(i)}}\Big)\tilde{\mathbf t}' \bmod p .$$
--   If $BP(\chi)=1$, then
--   $$F_\chi(\mathcal{RND}_p(BP)) = 0$$
--   for every choice of the randomness ("with probability 1").
--
--   This is the correctness of the randomization: evaluating the primal program against the dummy program recovers the output of $BP$.
--
--   **Formalization Note.** The statement holds for every sample $\omega$ of the randomness, which is what "with probability 1" means. Part (b) of the observation (if $BP(\chi)=0$ then $F_\chi\neq0$ except with probability $1/p$) is not formalized: with the $\gamma$-procedure for the bundling scalars, $\prod_i\alpha_{i,b_i}=0$ has probability about $2n/p$, so (b) as printed is not exact, and Theorem 6 does not use it.
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), p. 17, Section 4.2, observation (a)

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

namespace GGHRSW.ColoredMatrix

theorem observation_4_2a (p : ℕ) [Fact p.Prime] (bp : BP) (ω : Sample p bp)
    (χ : Fin bp.ℓ → Bool) (h : bp.eval χ = true) :
    Fchi bp ω χ = 0 := by sorry

end GGHRSW.ColoredMatrix
