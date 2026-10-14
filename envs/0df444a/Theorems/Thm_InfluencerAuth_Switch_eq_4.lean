-- Prove2me | Theorems.Thm_InfluencerAuth_Switch_eq_4
-- name    : InfluencerAuth.Switch.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:29.051982+00:00
-- url     : https://prove2.me/theorems/3a53b030-6a92-41d9-aa41-6fb21c8ceeff
-- title:
--   (4), §3.3, p. 6 — limit of dV̲/dA as A → 0: γφ/(r − γβ) if γβ < r, +∞ if γβ ≥ r
-- statement:
--   Let $0<\gamma<1$, $\varphi>1$ with $\gamma\varphi>1$, $\beta>0$ and $r>0$, and let $m(A)$ be the right side of (3). As awareness tends to zero from above, $m(A)$ tends to $\int_0^\infty e^{(\gamma\beta-r)s}\gamma\varphi\,ds$, which (4) and the sentence after it evaluate:
--
--   1. if $\gamma\beta<r$, then
--   $$
--   \lim_{A\to0^+} m(A)=\frac{\gamma\varphi}{r-\gamma\beta};
--   $$
--   2. if $\gamma\beta\ge r$, then $m(A)\to+\infty$ as $A\to0^+$.
--
--   The limit is the marginal value of awareness for a very small influencer who will be inauthentic from now on; comparing it with the gain from being inauthentic yields Condition 1.
--
--   **Formalization Note** "$A_t\to0$" is the right-neighbourhood filter at $0$, and "diverges to infinity" is divergence to $+\infty$ (`atTop`).
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), §3.3, (4) and the following sentence, p. 6

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model
import Definitions.Def_InfluencerAuth_Switch_ClosedForms

open MeasureTheory Set Filter Topology

namespace InfluencerAuth.Switch

/-- (4) (p. 6) and the sentence after it: the limit of (3) as awareness tends to zero. -/
theorem eq_4 (γ φ β r : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ)
    (hβ : 0 < β) (hr : 0 < r) (hγφ : 1 < γ * φ) :
    (γ * β < r →
      Tendsto (fun A => margValue γ φ β r A) (𝓝[>] (0 : ℝ)) (𝓝 (γ * φ / (r - γ * β)))) ∧
    (r ≤ γ * β →
      Tendsto (fun A => margValue γ φ β r A) (𝓝[>] (0 : ℝ)) atTop) := by sorry

end InfluencerAuth.Switch
