-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_revenue_equivalence
-- name    : MechanismDesign.IncentiveCompat.revenue_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:12:55.080834+00:00
-- url     : https://prove2.me/theorems/0fdfc763-cdda-4418-b4e5-d0ed3a654538
-- title:
--   Proposition 5.8 -- revenue equivalence on convex type spaces: transfers are unique up to a constant
-- statement:
--   Let the type set $\Theta$ be a nonempty convex subset of $\mathbb R^n$, let $A$ be a set of alternatives, and suppose that for every $a \in A$ the utility $u(a,\theta)$ is a convex function of $\theta$ on $\Theta$ that is also continuous on $\Theta$. Let $(q,t)$ be an incentive-compatible direct mechanism. Then a direct mechanism $(q,t')$ with the same decision rule is incentive-compatible if and only if there is $\tau \in \mathbb R$ with
--   $$t'(\theta) = t(\theta) + \tau \qquad \text{for all } \theta \in \Theta.$$
--
--   For a given implementable decision rule, the set of transfer rules that implement it is one function and all its parallel translations (Krishna and Maenner 2001).
--
--   **Formalization Note** Continuity of $u(a,\cdot)$ on $\Theta$ is added to the book's hypotheses; a convex function on a convex set is automatically continuous only on its relative interior, and without continuity at the boundary the statement is false. Example: $\Theta = [0,1]$, $A = \{a,b\}$, $u(a,0) = 5$, $u(a,\theta) = 0$ for $\theta > 0$, $u(b,\cdot) = 0$, $q(0) = a$ and $q(\theta) = b$ for $\theta > 0$; both $t \equiv 0$ and $t' = -\mathbf 1_{(0,1]}$ make $q$ incentive-compatible. Every utility convex on an open convex set containing $\Theta$ (for instance, the linear expected utility of lotteries) satisfies the added hypothesis.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.109, Proposition 5.8 (Krishna and Maenner 2001)

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.8 (Krishna–Maenner 2001; p.109), in the corrected form. Types form a nonempty
convex set `S ⊆ ℝⁿ`; for each alternative `a` the utility `w a` is convex on `S` and, in addition
to the book's hypotheses, continuous on `S` (without continuity at the relative boundary the
statement is false). If `(q, t)` is incentive-compatible, then `(q, t')` is incentive-compatible
if and only if `t' = t + τ` on `S` for some constant `τ`. -/
theorem revenue_equivalence {A : Type*} {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Convex ℝ S)
    (hSne : S.Nonempty) (w : A → (Fin n → ℝ) → ℝ) (hconv : ∀ a, ConvexOn ℝ S (w a))
    (hcont : ∀ a, ContinuousOn (w a) S) (q : S → A) (t : S → ℝ)
    (hIC : IsIC (fun (a : A) (θ : S) => w a (θ : Fin n → ℝ)) ⟨q, t⟩) (t' : S → ℝ) :
    IsIC (fun (a : A) (θ : S) => w a (θ : Fin n → ℝ)) ⟨q, t'⟩ ↔
      ∃ τ : ℝ, ∀ θ : S, t' θ = t θ + τ := by sorry

end MechanismDesign.IncentiveCompat
