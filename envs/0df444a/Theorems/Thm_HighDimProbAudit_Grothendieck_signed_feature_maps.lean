-- Prove2me | Theorems.Thm_HighDimProbAudit_Grothendieck_signed_feature_maps
-- name    : HighDimProbAudit.Grothendieck.signed_feature_maps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:36:56.998833+00:00
-- url     : https://prove2.me/theorems/231a0835-4158-43b9-bf76-a4a9deff8c1b
-- title:
--   Exercise 3.7.6 — signed analytic feature maps and both norms
-- statement:
--   Let $n\in\mathbb N$, let $a_k\in\mathbb R$, and let $f:\mathbb R\to\mathbb R$ satisfy the globally convergent representation $f(x)=\sum_{k=0}^\infty a_kx^k$ for every real $x$. Coefficients may have either sign. There are a real Hilbert space $H$ and transformations $\Phi,\Psi:\mathbb R^n\to H$ such that
--   $$\langle\Phi(u),\Psi(v)\rangle=f(\langle u,v\rangle)\qquad(u,v\in\mathbb R^n),$$
--   and, for every $u\in\mathbb R^n$,
--   $$\|\Phi(u)\|^2=\|\Psi(u)\|^2=\sum_{k=0}^\infty |a_k|\,\|u\|_2^{2k}.$$
--   The absolute-coefficient series converges to these squared norms. The same space and two maps satisfy all three identities on the whole Euclidean space. This result supplies norm control for the subsequent unit-sphere statement.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with their Euclidean inner product → EuclideanSpace ℝ (Fin n); reason: Fin n relabels the finite coordinates; the norm and inner product are the Euclidean ones
--   - encoding: there exist a Hilbert space H and transformations → existential carrier H, normed additive group and real inner product structures, completeness, then maps; reason: the chosen structures specify the real Hilbert space before every input vector; no linearity, continuity, separability or finite dimension is imposed
--   - encoding: a single convergent power series (3.29) for every real x → GlobalPowerSeries a f, namely ∀ x : ℝ, HasSum (fun k => a k * x ^ k) (f x); reason: this is the source’s global series convention, rather than merely local real analyticity or a total infinite sum
--   - encoding: both squared norms equal the displayed infinite sum → HasSum of the absolute-coefficient series to ‖Φ(u)‖², together with ‖Φ(u)‖² = ‖Ψ(u)‖²; reason: the two source norm identities are equivalent to this formulation; convergence is a conclusion, not an additional hypothesis
-- source:
--   Vershynin, High-Dimensional Probability: An Introduction with Applications in Data Science, Cambridge University Press, 2018, author-corrected electronic copy dated June 9, 2020, https://doi.org/10.1017/9781108231596, Exercise 3.7.6, with the series convention (3.29), printed p. 72 (PDF p. 80).

import Mathlib
import Definitions.Def_HighDimProbAudit_Grothendieck_GlobalSeries

set_option autoImplicit false

namespace HighDimProbAudit.Grothendieck

/-- Exercise 3.7.6, printed p. 72 / PDF p. 80. -/
theorem signed_feature_maps (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : GlobalPowerSeries a f) :
    ∃ (H : Type) (hN : NormedAddCommGroup H),
      letI := hN
      ∃ hI : InnerProductSpace ℝ H,
        letI := hI
        CompleteSpace H ∧ ∃ Φ Ψ : EuclideanSpace ℝ (Fin n) → H,
          (∀ u v, inner ℝ (Φ u) (Ψ v) = f (inner ℝ u v)) ∧
          (∀ u, HasSum (fun k : ℕ => |a k| * ‖u‖ ^ (2 * k)) (‖Φ u‖ ^ 2) ∧
            ‖Φ u‖ ^ 2 = ‖Ψ u‖ ^ 2) := by sorry

end HighDimProbAudit.Grothendieck
