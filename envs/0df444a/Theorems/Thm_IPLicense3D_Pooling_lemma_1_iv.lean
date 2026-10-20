-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_lemma_1_iv
-- name    : IPLicense3D.Pooling.lemma_1_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:38.992134+00:00
-- url     : https://prove2.me/theorems/3bcd413d-a6be-4d95-822f-4fe598161635
-- title:
--   Lemma 1(iv), p. 2691 — the surplus decreases more rapidly in r for larger buyers: ∂²S/∂λ∂r < 0
-- statement:
--   Under the standing assumptions of §3 (in particular $z \ge 0$), view buyer $i$'s surplus $S(\lambda; f, r)$ as a function of its demand rate $\lambda$ as well as of the license $(f,r)$. For every fixed fee $f$ and every royalty $r \ge 0$, the mixed partial derivative at the buyer's demand rate $\lambda_i$ is negative:
--   $$
--   \frac{\partial^2}{\partial\lambda\,\partial r} S(\lambda_i; f, r) < 0 .
--   $$
--
--   Thus a larger buyer's surplus falls faster as the royalty rises. For two buyers with $\lambda_1 < \lambda_2$ this gives $\partial_r S_2(0,r) < \partial_r S_1(0,r) < 0$, the single-crossing property used in Lemma 2.
--
--   **Formalization Note** The derivative is written as `deriv` in $\lambda$ of the `deriv` in $r$, evaluated at $\lambda = \lambda_i > 0$ and $r \ge 0$, where the surplus is smooth. The hypothesis $z \ge 0$ is needed: for sufficiently negative $z$ and small $\lambda$ the mixed derivative becomes positive.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2691, Lemma 1(iv); proof p. 2699

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace IPLicense3D.Pooling
open Model

theorem lemma_1_iv {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) (f r : ℝ) (hr : 0 ≤ r) :
    deriv (fun l => deriv (fun r' => M.surplusL l f r') r) (M.lam i) < 0 := by sorry

end IPLicense3D.Pooling
