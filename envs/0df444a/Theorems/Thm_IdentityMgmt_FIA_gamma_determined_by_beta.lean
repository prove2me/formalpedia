-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_gamma_determined_by_beta
-- name    : IdentityMgmt.FIA.gamma_determined_by_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:51.90499+00:00
-- url     : https://prove2.me/theorems/ac80fe7d-22a3-486d-b9ef-292caea6910b
-- title:
--   p. 26 (PDF 30) — in every FIA Markov equilibrium the slope γ*(β) ∈ (0,1) of the cut-off rule depends on β only
-- statement:
--   In the FIA identity-management game, let two quasi-linear Markov equilibria (cut-off rules $\theta_{n+1} = K + \gamma\theta_n$, expectations rules $\Psi(\theta) = C + \lambda\theta$, possibly different pivots $\tilde\theta$) have the same discount factor $\beta$. Then their slopes coincide:
--   $$\gamma_P = \gamma_Q.$$
--   Moreover the slope is strictly positive, $\gamma > 0$, in every equilibrium.
--
--   So the market-expansion speed $\gamma^*(\beta)$ is a function of the discount factor alone, independent of the privacy cost and of the pivot. This is what makes the threshold $\bar c^{FIA}$, which depends on $\gamma$, a function of $\beta$.
--
--   **Formalization Note.** The paper identifies $\gamma^*(\beta)$ as the root of its polynomial (29). That polynomial does not follow from the model as printed (the envelope derivative (23) has a sign slip), so the statement asserts only uniqueness and positivity, not any particular polynomial.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), p. 26 (PDF 30), display after Lemma 2 ("γ*(β) is the solution of the polynomial (29)")

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem gamma_determined_by_beta :
    (∀ P Q : Profile, P.IsMarkovEq → Q.IsMarkovEq → P.β = Q.β → P.γ = Q.γ) ∧
    (∀ P : Profile, P.IsMarkovEq → 0 < P.γ) := by sorry

end IdentityMgmt.FIA
