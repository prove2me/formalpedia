-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_6_4
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:04:07.647871+00:00
-- url     : https://prove2.me/theorems/f94aa5dc-47df-4a2c-b095-ef00f9275424
-- title:
--   Theorem 6.4 — c_r^π = w_r − Σ_{r′} w_{r′} cov^π(n_r, n_{r′}) / 𝔼^π(n_r)
-- statement:
--   In the setting of Theorem 6.1 (rates $\nu_r>0$, capacities $C\in\mathbb Z_+^J$, revenues $w_r\in\mathbb R$, stationary distribution (1.2)), let $c_r^\pi=W^\pi(\nu;C)-W^\pi(\nu;C-Ae_r)$ be the implied cost (6.3). Then for every route $r$
--   $$\mathbb E^\pi(n_r)\,c_r^\pi=\mathbb E^\pi(n_r)\,w_r-\sum_{r'}w_{r'}\operatorname{cov}^\pi(n_r,n_{r'}),$$
--   and hence, whenever $\mathbb E^\pi(n_r)>0$,
--   $$c_r^\pi=w_r-\frac{\sum_{r'}w_{r'}\operatorname{cov}^\pi(n_r,n_{r'})}{\mathbb E^\pi(n_r)}.$$
--
--   This expresses the implied costs through first and second moments of the stationary distribution, without a second partition function.
--
--   **Formalization Note** With positive rates, $\mathbb E^\pi(n_r)=0$ exactly when a call on route $r$ cannot fit ($C-Ae_r$ has a negative entry); there the printed quotient is undefined and both sides of the cross-multiplied identity are $0$.
--
--   Differences from the source:
--   - encoding: ν_r rates of the Poisson streams → hypothesis ν_r > 0 for all r; reason: standing positive-rate assumption of the model
--   - encoding: the quotient form, whose denominator is 𝔼^π(n_r) → the quotient form under the hypothesis 𝔼^π(n_r) > 0; reason: the hypothesis excludes only the cases where the printed quotient is undefined (𝔼^π(n_r) = 0)
--   - generalization: only the quotient form → also the cross-multiplied identity 𝔼^π(n_r) c_r^π = 𝔼^π(n_r) w_r − Σ_{r'} w_{r'} cov^π(n_r, n_{r'}) for every route; reason: on 𝔼^π(n_r) > 0 it is equivalent to the printed formula; it adds the zero-occupancy routes, where both sides vanish
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 369, Theorem 6.4; c_r^π by (6.3), p. 368

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 6.4** (Hunt). `c_r^π = w_r − (Σ_{r'} w_{r'} cov^π(n_r, n_{r'})) / 𝔼^π(n_r)`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 369, Theorem 6.4; `c_r^π` by (6.3), p. 368.

**Formalization Note.** Two clauses: the cross-multiplied identity
`𝔼^π(n_r) c_r^π = 𝔼^π(n_r) w_r − Σ_{r'} w_{r'} cov^π(n_r, n_{r'})`, for every route, and the
printed quotient form whenever its denominator `𝔼^π(n_r)` is positive. With positive rates,
`𝔼^π(n_r) = 0` exactly when a call on route `r` does not fit (`C − Ae_r` has a negative entry);
there the printed quotient is undefined and only the cross-multiplied identity is asserted.
Expectations and covariances are under the exact stationary distribution (1.2). -/
theorem theorem_6_4 {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 < ν r) (C : Fin J → ℕ) (w : Fin R → ℝ) (r : Fin R) :
    expect A ν (capInt C) (fun n => (n r : ℝ)) * impliedCost A ν (capInt C) w r =
        expect A ν (capInt C) (fun n => (n r : ℝ)) * w r -
          ∑ r', w r' * covariance A ν (capInt C) r r' ∧
      (0 < expect A ν (capInt C) (fun n => (n r : ℝ)) →
        impliedCost A ν (capInt C) w r =
          w r - (∑ r', w r' * covariance A ν (capInt C) r r') /
            expect A ν (capInt C) (fun n => (n r : ℝ))) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
