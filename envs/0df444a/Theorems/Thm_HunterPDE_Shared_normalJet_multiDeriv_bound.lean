-- Prove2me | Theorems.Thm_HunterPDE_Shared_normalJet_multiDeriv_bound
-- name    : HunterPDE.Shared.normalJet_multiDeriv_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T15:49:16.085868+00:00
-- url     : https://prove2.me/theorems/d681dc08-6d23-4c62-b660-61088defd7d8
-- title:
--   Boundary Taylor bound for mixed derivatives with vanishing normal jets
-- statement:
--   Let $\psi\in C_c^\infty(\mathbb R^n)$, fix a coordinate $i$ and a nonnegative integer $k$, and suppose $\partial_i^r\psi=0$ on $x_i=0$ for every $r<k$. For every multi-index $\beta$ there is a nonnegative constant $C$ such that
--   $$|\partial^\beta\psi(x)|\le C|x_i|^{\max(k-\beta_i,0)}\qquad(x\in\mathbb R^n).$$
--   There is no restriction on the tangential entries of $\beta$. When $\beta_i\ge k$ the exponent is zero. The constant may depend on the function, derivative order and normal direction, and is uniform over the whole space. This estimate expresses the quantitative effect of boundary jet vanishing and can be reused independently of any cutoff or Sobolev extension.
-- source:
--   Derived mixed-partial boundary Taylor estimate: Mathlib.Analysis.Calculus.Taylor.taylor_mean_remainder_bound, pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/Taylor.lean . Apply Taylor on normal lines after smooth mixed-partial commutation; compact support gives uniform derivative bounds. Auxiliary for S.-J. Oh, Math 222A notes (March 19, 2024), Proposition 11.13 Step 2, printed p.158, https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf ; this interface is a derived calculus assertion, not a verbatim statement in the notes.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.normalJet_multiDeriv_bound
    {n : ℕ} (i : Fin n) (k : ℕ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hb : ∀ r : ℕ, r < k → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0)
    (β : Fin n → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ‖multiDeriv ψ β x‖ ≤ C * ‖x i‖ ^ (k - β i) := by sorry
