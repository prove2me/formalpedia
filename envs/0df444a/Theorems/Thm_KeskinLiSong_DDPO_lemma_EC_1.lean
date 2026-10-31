-- Prove2me | Theorems.Thm_KeskinLiSong_DDPO_lemma_EC_1
-- name    : KeskinLiSong.DDPO.lemma_EC_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:49:18.727727+00:00
-- url     : https://prove2.me/theorems/38fd05e9-5197-4e35-a49e-c0edd18b46a0
-- title:
--   Lemma EC.1 — optimal inventory by one-sided derivatives
-- statement:
--   Consider the model of Sections 2–3: real compact price and inventory intervals, an increasing C2 link, piecewise-constant demand parameters with C separated changes, independent centered locally light-tailed noise, and independent beta perishability. Costs satisfy the printed restriction. Estimators and policies are the concrete DDPO constructions, with measurable choices among genuine optimizers. The statement includes existence of a stock optimum satisfying both sign-set equalities, and both one-sided derivative identities at every y in Y. Unconstrained removes only the lower bound y>=x, not the box Y. Cdf atoms are permitted. Empty derivative-sign sets use their extended-real values rather than a fabricated real zero.
--
--   $$
--   y_t^u=\inf\{y\in Y:H_+^{\prime}(y)\ge0\}=\sup\{y\in Y:H_-^{\prime}(y)<0\}.
--   $$
--
--   The full source statement, including all definitions and clauses, is:
--
--   LEMMA EC.1. For p_t∈P, θ_t∈Θ, ξ∈Ξ, the unconstrained optimal order-up-to level in period t is
--   given by
--   y_t^u(p_t;θ_t,ξ)=inf{y_t∈Y : H′_+(y_t;p_t,θ_t,ξ)≥0}
--    =sup{y_t∈Y : H′_−(y_t;p_t,θ_t,ξ)<0}, (EC.1)
--   where H′_+(y_t;p_t,θ_t,ξ)=(h−c+b+p_t)E_{q|ξ}[(1−q_t)F_ε(z_t(q_t))]
--    −(b+p_t)(1−E_{q|ξ}[q_t])+(wE_{q|ξ}[q_t]+c)
--   and H′_−(y_t;p_t,θ_t,ξ)=(h−c+b+p_t)E_{q|ξ}[(1−q_t)F_ε(z_t(q_t)−)]
--    −(b+p_t)(1−E_{q|ξ}[q_t])+(wE_{q|ξ}[q_t]+c)
--   are the right and left derivatives of H(·;p_t,θ_t,ξ) at y_t, with z_t(q_t)=(1−q_t)y_t−g(X_tᵀθ_t) and F_ε(x−)
--   denotes the left limit of F_ε at x.
--
--   Differences from the source:
--   - generalization: the surrounding model supposes an interior FIA optimum exists → this statement does not require an FIA existence premise; reason: adding that source premise specializes the statement; its estimators, proxies, derivatives or unconstrained-regret contributions do not use the FIA benchmark
--   - encoding: infimum and supremum of derivative-sign subsets of Y → equalities in EReal and explicit one-sided derivative predicates; reason: empty sign sets retain +infinity or -infinity; no default zero or extra nonemptiness premise conceals boundary failures
--   - reading: the link g is increasing → g is nondecreasing and twice continuously differentiable; reason: increasing is read in its weak monotonicity sense; no strictly positive derivative or inverse-sensitivity assumption is printed
--   - encoding: the optimal level is given by the two sign-set expressions → there exists a genuine stock optimizer equal to both expressions; reason: the page identifies an optimizer; it does not separately assert uniqueness or that every optimizer must equal the selected level
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), Lemma EC.1, printed p. ec1 (PDF p. 33)

import Definitions.Def_KeskinLiSong_DDPO_TailEvents

open MeasureTheory ProbabilityTheory Set

namespace KeskinLiSong.DDPO

theorem lemma_EC_1 (A : Model) (theta xi : Vector 2) (p : ℝ)
    (hp : p ∈ A.P) (htheta : theta ∈ A.Theta) (hxi : xi ∈ A.Xi) :
    (∃ y, StockOptimum A A.noise.law theta xi p y ∧
      (y : EReal) = rightSignInf A theta xi p ∧
      (y : EReal) = leftSignSup A theta xi p) ∧
    (∀ y ∈ A.Y,
      HasDerivWithinAt (H A A.noise.law theta xi p)
        (slope true A theta xi p y) (Ici y) y ∧
      HasDerivWithinAt (H A A.noise.law theta xi p)
        (slope false A theta xi p y) (Iic y) y) := by sorry

end KeskinLiSong.DDPO
