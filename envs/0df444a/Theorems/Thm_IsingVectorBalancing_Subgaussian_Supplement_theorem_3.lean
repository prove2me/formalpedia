-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_Supplement_theorem_3
-- name    : IsingVectorBalancing.Subgaussian.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:19:55.348199+00:00
-- url     : https://prove2.me/theorems/88340d51-58a8-40c9-857a-509a8adde094
-- title:
--   Theorem 3 — Entrywise-tanh largest-eigenvalue criterion for arbitrary-field Ising Glauber dynamics
-- statement:
--   Let $n\ge1$, let $J\in\mathbb R^{n\times n}$ be symmetric with zero diagonal and let $h\in\mathbb R^n$ be any external field. On the sign cube use the Gibbs law $\mu_{J,h}(\sigma)\propto\exp(\sigma^T J\sigma/2+h^T\sigma)$. Form the entrywise matrix $T_{ij}=\tanh(J_{ij})$ and its algebraically largest eigenvalue $\lambda_{\max}(T)$. If $\lambda_{\max}(T)<1$, then its discrete-time random-scan heat-bath kernel $P$ satisfies
--
--   $$\operatorname{gap}(P)\ge\frac{1-\lambda_{\max}(T)}n.$$
--
--   This companion theorem permits interactions of either sign and arbitrary fields. It is not used in the proof of the mission's concentration goal.
--
--   Differences from the source:
--   - encoding: finite sets [n] and [q], real Euclidean vectors and finite expectations → Fin indices, EuclideanSpace, and finite sums; reason: the carriers and values are unchanged; Bool encodes the binary signs when present
--   - encoding: gap(P) bounded below on the feasible state space → the published finite Poincaré inequality with rates equal to the discrete transition matrix P; reason: its Laplacian is I−P on the support, so no time rescaling or irreducibility premise is introduced; singleton support is retained
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 2 (PDF 3), Theorem 3, (2); proof p. 16 (PDF 17)

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_GeneralIsing
import Definitions.Def_mm_mcmc
import Definitions.Def_SubsetConvFPRAS_ReversibleChain

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Theorem 3, p.2/PDF3. No absolute values in the spectral criterion. -/
theorem theorem_3 {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (h : Fin n → ℝ) (hT : largestEigenvalue (tanhMatrix J) < 1) :
    SubsetConvFPRAS.HasPoincare (isingLaw J h) (MarkovMixing.glauber (isingLaw J h))
      ((1 - largestEigenvalue (tanhMatrix J)) / (n : ℝ)) := by sorry

end IsingVectorBalancing.Subgaussian.Supplement
