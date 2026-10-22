-- Prove2me | Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_5
-- name    : LoopTwoGroup.Equiv.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:47.4881+00:00
-- url     : https://prove2.me/theorems/c7706347-d901-47da-b267-66273d7d17e3
-- title:
--   Lemma 5.5 — EΩ𝔤 embeds as the strict kernel of φ
-- statement:
--   For the endpoint homomorphism $\phi:\mathcal P_k\mathfrak g\to\mathfrak g_k$ of Lemma 5.4, there is a homomorphism $\lambda:E\Omega\mathfrak g\to\mathcal P_k\mathfrak g$ given by
--   $$\lambda_0(\ell)=\ell,\qquad \lambda_1(\ell)=(\ell,0),\qquad
--     \lambda_2(\ell_1,\ell_2)=\left(0,2k\int_0^{2\pi}\langle\ell_1,\ell_2'\rangle\,d\theta\right).$$
--   The maps in degrees zero and one are injective, and in each degree the image of $\lambda$ is exactly the kernel of $\phi$. This identifies the left part of the sequence in Theorem 5.1.
--
--   **Formalization Note** The theorem existentially supplies both $\phi$ and $\lambda$ with the displayed components, so its kernel assertion has a specified quotient map.
-- source:
--   Baez–Crans–Stevenson–Schreiber, From Loop Groups to 2-Groups, arXiv:math/0504123v3, pp. 28–29, Lemma 5.5 and its component display on p. 29

import Mathlib
import Definitions.Def_LoopTwoGroup_Equiv_Model

namespace LoopTwoGroup.Equiv

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

/-- Lemma 5.5, pp. 28–29: the displayed inclusion identifies the strict kernel. -/
theorem lemma_5_5 (L : InvLieBracket g) (k : ℝ) :
    ∃ (Φ : LInfHom (Pk L k) (gk L k)) (Λ : LInfHom (EOmega L) (Pk L k)),
      PhiComponents L k Φ ∧ LambdaComponents L k Λ ∧
      Function.Injective Λ.f0 ∧ Function.Injective Λ.f1 ∧
      LinearMap.range Λ.f0 = LinearMap.ker Φ.f0 ∧
      LinearMap.range Λ.f1 = LinearMap.ker Φ.f1 := by sorry

end LoopTwoGroup.Equiv
