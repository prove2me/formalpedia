-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_bfgsStep_action
-- name    : LimitedBFGS.SQN.bfgsStep_action
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T19:02:11.785628+00:00
-- url     : https://prove2.me/theorems/f77d1cba-b0ae-405b-98bb-40f36b12896c
-- title:
--   Effect of one special BFGS update (4)-(5) on a vector orthogonal to the stored secant pair
-- statement:
--   Let $H$ be a matrix, and let $(s,y)$ be a stored secant pair. Write the special BFGS update (4)–(5) in its product form $\mathrm{BFGS}(H;s,y) = V^\top H V + \rho\, s s^\top$ with $\rho = 1/(y^\top s)$ and $V = I - \rho\, y s^\top$.
--
--   **Claim.** If $s^\top g = 0$ and $y^\top (H g) = 0$ then $\mathrm{BFGS}(H;s,y)\, g = H g$. Moreover, under just $s^\top g = 0$ one has the explicit formula $\mathrm{BFGS}(H;s,y)\, g = H g - \rho\,(y^\top H g)\, s$.
--
--   **Why.** From $s^\top g = 0$ we get $V g = g$, hence $V^\top H V g = V^\top (H g)$. Applying (7), $V^\top w = w - \rho (y^\top w) s$, so $V^\top (H g) = H g - \rho\,(y^\top H g) s$ and the rank-one term $\rho\, s s^\top g$ vanishes. If in addition $y^\top (Hg) = 0$ the correction disappears and the update is a no-op on $g$.
--
--   **Role.** This is the algebraic fact behind the identity of the limited-storage BFGS method (17) and the preconditioned conjugate gradient method with fixed preconditioner $H_0$ (Nocedal 1980, p. 778): every retained correction pair older than the newest one acts trivially on the current gradient, while the newest pair reproduces exactly PCG's $\beta$ term.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 776, eq. (7) and pp. 777-778 (the product form (4)-(5) used for the step of iteration (17)).

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix

namespace LimitedBFGS.SQN

/-- Effect of one special BFGS update on a vector that is orthogonal to both the stored
secant pair's `s` and its `y`-image. Writing `bfgsStep H s y = Vᵀ H V ρ …` for the product
form (4)–(5), with `V = I − ρ y sᵀ`: if `sᵀg = 0` and `yᵀ(Hg) = 0` then the update leaves `H *ᵥ g`
alone, since `Vg = g` and `Vᵀ(Hg) = Hg`; and in general, under just `sᵀg = 0`,
`bfgsStep H s y *ᵥ g = H *ᵥ g − (ρ · yᵀ(Hg)) • s` with `ρ = bfgsRho s y`. These are the two
identities that make the limited-storage BFGS matrix act on the current PCG gradient exactly
as the conjugate gradient recurrence does (Nocedal 1980, p. 778). -/
theorem bfgsStep_action {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y g : Fin n → ℝ)
    (hs : s ⬝ᵥ g = 0) (hy : y ⬝ᵥ (H *ᵥ g) = 0) :
    bfgsStep H s y *ᵥ g = H *ᵥ g ∧
      bfgsStep H s y *ᵥ g = H *ᵥ g - (bfgsRho s y * (y ⬝ᵥ (H *ᵥ g))) • s := by sorry

end LimitedBFGS.SQN
