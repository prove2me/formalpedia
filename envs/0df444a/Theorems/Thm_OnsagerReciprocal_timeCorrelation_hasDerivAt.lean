-- Prove2me | Theorems.Thm_OnsagerReciprocal_timeCorrelation_hasDerivAt
-- name    : OnsagerReciprocal.timeCorrelation_hasDerivAt
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:59:52.159827+00:00
-- url     : https://prove2.me/theorems/7d528fbd-ee21-4819-8caf-73252c29d06c
-- title:
--   Derivative of the time correlation $\langle\xi_i(t)x_k\rangle$
-- statement:
--   Let $\beta$ be a positive definite real symmetric $n\times n$ matrix and $\lambda$ a real $n\times n$ matrix, with $\gamma=\lambda\beta^{-1}$. Average over the Gaussian fluctuation distribution $w(x)\propto\exp(-\tfrac12\beta_{ik}x_ix_k)$, and let $\xi(t;x)=e^{-t\lambda}x$, $\Xi(t;x)=\beta\,\xi(t;x)$. Then for all indices $i,k$ and all $t\in\mathbb R$, the time correlation $C_{ik}(t)=\langle\xi_i(t;x)\,x_k\rangle$ is differentiable at $t$ and
--   $$\frac{d}{dt}\big\langle\xi_i(t)\,x_k\big\rangle=-\gamma_{il}\,\big\langle\Xi_l(t)\,x_k\big\rangle .$$
--   This is the "differentiate and substitute" step of the proof of Onsager's principle.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" and its "Proof" subsection (pp. 5-6 of the PDF export), following L. D. Landau, E. M. Lifshitz, Statistical Physics, Part 1 (1975)

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem timeCorrelation_hasDerivAt {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (i k : Fin n) (t : ℝ) :
    HasDerivAt (fun s => timeCorrelation β lam s i k)
      (-∑ l : Fin n, kineticCoeff β lam i l *
        fluctuationAverage β (fun x => meanConjugate β lam t x l * x k)) t := by sorry
end OnsagerReciprocal
