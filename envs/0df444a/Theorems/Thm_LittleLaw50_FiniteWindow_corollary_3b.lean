-- Prove2me | Theorems.Thm_LittleLaw50_FiniteWindow_corollary_3b
-- name    : LittleLaw50.FiniteWindow.corollary_3b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:01.972101+00:00
-- url     : https://prove2.me/theorems/2fa349f9-4c4e-42f5-aa1f-f86c6326c841
-- title:
--   §2.2.3, Corollary (3)(b), p. 539 — with λ = Σ_k λ_k, L = Σ_k L_k and W = Σ_k (λ_k/λ) W_k, L = λW
-- statement:
--   In the setting of Corollary (3)(a): one sample path observed over $[0, T]$ with $0 < T < \infty$, items with $a_i \le d_i$, divided into mutually exclusive classes $k = 1, \dots, K$, and $L_k$, $\lambda_k$, $W_k$ the LL parameters of class $k$ computed from the class-$k$ items alone. Let
--
--   $$\lambda = \sum_k \lambda_k, \qquad L = \sum_k L_k, \qquad W = \sum_k \frac{\lambda_k}{\lambda}\, W_k .$$
--
--   Then
--
--   $$L = \lambda W.$$
--
--   The aggregate parameters built from the class-wise ones satisfy Little's Law again, with $W$ the arrival-weighted average of the class waits.
--
--   **Formalization Note** $L_k$, $\lambda_k$ and $W_k$ are computed from the sample path (they are not free numbers). If $\lambda = 0$ (no class has an item in the system over $[0, T]$), Lean's $\lambda_k/\lambda$ is $0$ and both sides are $0$.
-- source:
--   Little, Little's Law as Viewed on Its 50th Anniversary, Oper. Res. 59(3) (2011), DOI 10.1287/opre.1110.0940, p. 539, §2.2.3, Corollary (3)(b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_LittleLaw50_FiniteWindow_Window

namespace LittleLaw50.FiniteWindow

/-- **§2.2.3, Corollary (3)(b)** (Little 2011, p. 539). With `L_k, λ_k, W_k` the LL parameters of
class `k`, put `λ = Σ_k λ_k`, `L = Σ_k L_k` and `W = Σ_k (λ_k/λ) W_k`. Then `L = λ W`. -/
theorem corollary_3b {M K : ℕ} (a d : Fin M → ℝ) (c : Fin M → Fin K) (T : ℝ) (hT : 0 < T)
    (had : ∀ i, a i ≤ d i) :
    (∑ k, Lw (classItems c k) a d T)
      = (∑ k, lamw (classItems c k) a d T)
        * ∑ k, (lamw (classItems c k) a d T / ∑ k', lamw (classItems c k') a d T)
            * Ww (classItems c k) a d T := by sorry

end LittleLaw50.FiniteWindow
