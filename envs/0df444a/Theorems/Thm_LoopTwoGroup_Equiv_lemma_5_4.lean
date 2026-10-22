-- Prove2me | Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_4
-- name    : LoopTwoGroup.Equiv.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:48.372277+00:00
-- url     : https://prove2.me/theorems/09ffa5d9-f0d9-4684-bbee-af2bd9fb6b4f
-- title:
--   Lemma 5.4 — endpoint homomorphism from P_k𝔤 to 𝔤_k
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real simple Lie algebra with invariant inner product, and let $k\in\mathbb R$. There is a 2-term $L_\infty$ homomorphism $\phi:\mathcal P_k\mathfrak g\to\mathfrak g_k$ with components
--   $$\phi_0(p)=p(2\pi),\qquad \phi_1(\ell,c)=c,\qquad
--     \phi_2(p_1,p_2)=k\int_0^{2\pi}\bigl(\langle p_2,p_1'\rangle-\langle p_2',p_1\rangle\bigr)\,d\theta.$$
--   This is the quotient map in the strictly exact sequence of Theorem 5.1. Its degree-two component includes the boundary-sensitive skew integral.
--
--   **Formalization Note** Paths are smooth on the closed interval and extended constantly beyond it. Their derivatives in the integral are one-sided at the endpoints.
-- source:
--   Baez–Crans–Stevenson–Schreiber, From Loop Groups to 2-Groups, arXiv:math/0504123v3, pp. 26–27, Lemma 5.4 and the display at the top of p. 27

import Mathlib
import Definitions.Def_LoopTwoGroup_Equiv_Model

namespace LoopTwoGroup.Equiv

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

/-- Lemma 5.4, pp. 26–27: the path endpoint homomorphism with its integral component. -/
theorem lemma_5_4 (L : InvLieBracket g) (k : ℝ) :
    ∃ Φ : LInfHom (Pk L k) (gk L k), PhiComponents L k Φ := by sorry

end LoopTwoGroup.Equiv
