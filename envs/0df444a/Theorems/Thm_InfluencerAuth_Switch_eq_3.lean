-- Prove2me | Theorems.Thm_InfluencerAuth_Switch_eq_3
-- name    : InfluencerAuth.Switch.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:46.005204+00:00
-- url     : https://prove2.me/theorems/db6e7f56-c304-4a23-8424-ce019754a913
-- title:
--   (3), §3.3, p. 6 — dV̲(A)/dA = ∫₀^∞ e^{−(γβ+r)s}γφ/[A + (1 − A)e^{−γβs}]² ds
-- statement:
--   Let $0<\gamma<1$, $\varphi>1$ with $\gamma\varphi>1$, $\beta>0$ and $r>0$. The value $\underline V$ of always being inauthentic (Lemma 3) is differentiable at every awareness level $A\in(0,1)$, with
--   $$
--   \frac{d\underline V(A)}{dA}=\int_0^\infty \frac{e^{-(\gamma\beta+r)s}\,\gamma\varphi}{\big[A+(1-A)e^{-\gamma\beta s}\big]^2}\,ds .
--   $$
--   This is the marginal value of awareness for an influencer who will be inauthentic from now on. Proposition 1 locates the switch to inauthenticity where it equals $(\gamma\varphi-1)/((1-\gamma)\beta(1-A))$.
--
--   **Formalization Note** $\underline V$ and the right side are the definitions `inauthValue` and `margValue`; the derivative is two-sided and stated only at interior points $A\in(0,1)$.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), §3.3, (3), p. 6

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model
import Definitions.Def_InfluencerAuth_Switch_ClosedForms

open MeasureTheory Set Filter Topology

namespace InfluencerAuth.Switch

/-- (3) (p. 6): the derivative of the always-inauthentic value. -/
theorem eq_3 (γ φ β r : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ)
    (hβ : 0 < β) (hr : 0 < r) (hγφ : 1 < γ * φ) :
    ∀ A ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun a => inauthValue γ φ β r a) (margValue γ φ β r A) A := by sorry

end InfluencerAuth.Switch
