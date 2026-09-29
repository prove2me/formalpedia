-- Prove2me | Theorems.Thm_Larmor_lw_source_free
-- name    : Larmor.lw_source_free
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T01:18:26.761974+00:00
-- url     : https://prove2.me/theorems/d27ba433-a811-41e2-a1ea-5fcfa697a807
-- title:
--   The Liénard–Wiechert fields solve the source-free Maxwell equations off the worldline
-- statement:
--   **The Liénard–Wiechert fields are a vacuum solution away from the charge.** Let $\varepsilon_0>0$ and $c>0$, and let the worldline $w$ of a point charge $q$ be smooth and Lipschitz with a constant $K<c$. Suppose given, for each observation event $(t,x)$, a time $t_r(t,x)$ satisfying the retardation relation $t_r\le t$, $c\,(t-t_r)=\|x-w(t_r)\|$ (by the uniqueness theorem this time is unique, so the assignment is canonical). Let $E$ and $B$ denote the Liénard–Wiechert fields built from $w$ and this retarded time.
--
--   Then at every event $(t,x)$ at which the observation point differs from the retarded position of the charge, $x\ne w(t_r(t,x))$, all four source-free Maxwell equations hold:
--
--   $$\nabla\cdot E=0,\qquad \nabla\cdot B=0,\qquad \nabla\times E=-\,\partial_tB,\qquad \nabla\times B=\frac{1}{c^2}\,\partial_tE .$$
--
--   This is the statement that the Larmor derivation is a derivation from electromagnetism rather than from a postulated field formula: away from the point charge itself the Liénard–Wiechert expressions are genuine vacuum solutions, so the energy flux computed from them is the flux of an actual electromagnetic field.
--
--   **Formalization Note** Smoothness of the worldline is assumed to all orders; the spatial operators are applied to the field at frozen observation time, and the time derivatives are taken at a frozen observation point, in both cases with the retarded time varying as a function of the observation event.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section ("The electric and magnetic fields are given by the Liénard–Wiechert field equations"); J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, §14.1, eq. (14.14), where these fields are obtained as the retarded solution of Maxwell's equations for a point source.

import Definitions.Def_Larmor_em_fields
import Definitions.Def_Larmor_lienard_wiechert

namespace Larmor

theorem lw_source_free (q ε₀ c : ℝ) (hε : 0 < ε₀) (hc : 0 < c) (K : NNReal) (hK : (K : ℝ) < c)
    (w : ℝ → Vec) (hw : LipschitzWith K w) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (tr : ℝ → Vec → ℝ) (htr : ∀ t x, IsRetardedTime c w t x (tr t x))
    (t : ℝ) (x : Vec) (hx : x ≠ w (tr t x)) :
    divg (fun y => lwE q ε₀ c w (tr t y) y) x = 0 ∧
      divg (fun y => lwB q ε₀ c w (tr t y) y) x = 0 ∧
      curl (fun y => lwE q ε₀ c w (tr t y) y) x
        = -deriv (fun s => lwB q ε₀ c w (tr s x) x) t ∧
      curl (fun y => lwB q ε₀ c w (tr t y) y) x
        = (1 / c ^ 2) • deriv (fun s => lwE q ε₀ c w (tr s x) x) t := by sorry

end Larmor
