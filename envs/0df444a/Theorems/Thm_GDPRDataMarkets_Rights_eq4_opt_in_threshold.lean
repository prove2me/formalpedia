-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_eq4_opt_in_threshold
-- name    : GDPRDataMarkets.Rights.eq4_opt_in_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:10.154557+00:00
-- url     : https://prove2.me/theorems/19c9258a-9de6-4cd8-a383-295692e5fdd2
-- title:
--   Eq. (4), p. 14 — a consumer purchases and opts in iff v ≥ v*_M(p₁) = max{c/(δσ), (p₁ + c)/(1 + δσ)}
-- statement:
--   Assume $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$. Fix a strategy profile, a first-period price $p_1$ and a consumer $v\in[0,1]$, and suppose the firm's personalized price for $v$ at the anticipated basic price $q=p^*_{2M}(p_1)$ is the one of eq. (2), $r=(\mu-\sigma)v+\min\{v,q\}-c$. Then purchasing and opting in is a best first-period action for $v$ (at least as good as purchasing without opting in and as not purchasing) if and only if
--   $$v\ \ge\ \max\Big\{\frac{c}{\delta\sigma},\ \frac{p_1+c}{1+\delta\sigma}\Big\}=v^*_M(p_1).$$
--
--   The first term is where the expected personalization surplus $\delta\sigma v$ covers the breach cost; the second is where opting in beats not buying at all. The threshold does not depend on the second-period basic price.
--
--   **Formalization Note** The consumer's payoffs are the model's first-period utilities, with the expectation over $\kappa$ taken inside the period-2 utility $\max\{(1+\kappa)v-r-c,\ \max\{v-q,0\}\}$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 14, eq. (4)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- Eq. (4), p. 14: if the firm prices the personalized good to consumer `v` by eq. (2) at the
anticipated basic price `p*_2M(p₁)`, then purchasing and opting in is a best first-period action for
`v` exactly when `v ≥ v*_M(p₁) = max{c/(δσ), (p₁ + c)/(1 + δσ)}`. -/
theorem eq4_opt_in_threshold (P : Params) (hS : P.Standing) (s : Profile) (p1 v : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hr : s.r v (s.p2 p1) = (P.mu - P.sigma) * v + min v (s.p2 p1) - P.c) :
    (U1 P s p1 v .buy ≤ U1 P s p1 v .optIn ∧ U1 P s p1 v .none ≤ U1 P s p1 v .optIn)
      ↔ vStar P p1 ≤ v := by sorry

end GDPRDataMarkets.Rights
