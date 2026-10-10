-- Prove2me | Theorems.Thm_OnsagerReciprocal_conjugate_fluctuation_average
-- name    : OnsagerReciprocal.conjugate_fluctuation_average
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:01:52.741832+00:00
-- url     : https://prove2.me/theorems/89bc7b68-a660-4287-b343-914c0082d0db
-- title:
--   $\langle X_i x_k\rangle=\delta_{ik}$
-- statement:
--   Let $\beta$ be a positive definite real symmetric $n\times n$ matrix, and let the fluctuations $x\in\mathbb R^n$ be distributed with the Gaussian density $w(x)=\tilde A\exp(-\tfrac12\beta_{ik}x_ix_k)$, where $\tilde A$ normalizes $w$. With the conjugate quantities $X_i=\beta_{ik}x_k$, for all indices $i,k$,
--   $$\langle X_i\,x_k\rangle=\delta_{ik}.$$
--   Equivalently, the covariance matrix of the fluctuations is $\beta^{-1}$. This identity is used at the last step of the proof of Onsager's principle.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" and its "Proof" subsection (pp. 5-6 of the PDF export), following L. D. Landau, E. M. Lifshitz, Statistical Physics, Part 1 (1975)

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem conjugate_fluctuation_average {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (i k : Fin n) :
    fluctuationAverage β (fun x => conjugate β x i * x k) = if i = k then 1 else 0 := by sorry
end OnsagerReciprocal
