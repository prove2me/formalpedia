-- Prove2me | Theorems.Thm_OnsagerReciprocal_reciprocity_at_time_zero
-- name    : OnsagerReciprocal.reciprocity_at_time_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:02:21.802987+00:00
-- url     : https://prove2.me/theorems/967047b4-0c69-407b-aabd-c5934f58fc92
-- title:
--   Time reversal at $t=0$: $\gamma_{il}\langle X_lx_k\rangle=\gamma_{kl}\langle X_lx_i\rangle$
-- statement:
--   Let $\beta$ be a positive definite real symmetric $n\times n$ matrix, $\lambda$ a real $n\times n$ matrix and $\gamma=\lambda\beta^{-1}$. Average over the Gaussian fluctuation distribution $w(x)\propto\exp(-\tfrac12\beta_{ik}x_ix_k)$, let $\xi(t;x)=e^{-t\lambda}x$ and $X=\beta x$. Assume the **symmetry of fluctuations under time reversal**
--   $$\langle\xi_i(t)\,x_k\rangle=\langle x_i\,\xi_k(t)\rangle\qquad\text{for all }t\ge0\text{ and all }i,k .$$
--   Then for all $i,k$,
--   $$\gamma_{il}\,\langle X_l\,x_k\rangle=\gamma_{kl}\,\langle X_l\,x_i\rangle .$$
--   This is the identity obtained by differentiating the time-reversal relation and putting $t=0$.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" and its "Proof" subsection (pp. 5-6 of the PDF export), following L. D. Landau, E. M. Lifshitz, Statistical Physics, Part 1 (1975)

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem reciprocity_at_time_zero {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef)
    (hrev : ∀ t : ℝ, 0 ≤ t → ∀ i k : Fin n,
      timeCorrelation β lam t i k = timeCorrelation β lam t k i)
    (i k : Fin n) :
    ∑ l : Fin n, kineticCoeff β lam i l *
        fluctuationAverage β (fun x => conjugate β x l * x k) =
      ∑ l : Fin n, kineticCoeff β lam k l *
        fluctuationAverage β (fun x => conjugate β x l * x i) := by sorry
end OnsagerReciprocal
