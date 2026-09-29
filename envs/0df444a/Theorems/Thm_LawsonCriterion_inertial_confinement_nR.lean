-- Prove2me | Theorems.Thm_LawsonCriterion_inertial_confinement_nR
-- name    : LawsonCriterion.inertial_confinement_nR
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:20:10.439205+00:00
-- url     : https://prove2.me/theorems/bf5e059e-ec54-4aec-a4d2-e60e07c33f79
-- title:
--   Inertial confinement form: $nR \ge 12\,T^{3/2} / (E_{\mathrm{ch}} \langle\sigma v\rangle \sqrt{m_i})$
-- statement:
--   For inertial confinement the criterion is more useful in terms of the size of the fuel assembly. A good approximation for the confinement time is the time an ion needs to travel a distance $R$ at its thermal speed $v_{th} = \sqrt{T/m_i}$, that is $\tau_E = R\sqrt{m_i/T}$, where $m_i$ is the mean ionic mass and $T$ is again the temperature in energy units. Substituting this into the Lawson criterion converts the bound on $n\tau_E$ into a bound on the areal quantity $nR$:
--
--   $$n\,R \;\ge\; \frac{12\,T^{3/2}}{E_{\mathrm{ch}}\,\langle\sigma v\rangle\,\sqrt{m_i}}.$$
--
--   Multiplied by the ionic mass this is the familiar $\rho R$ requirement of inertial-confinement fusion.
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Inertial confinement", the approximation τ_E ≈ R √(m_i / k_B T) and the resulting bound n·R ≳ (12 / E_ch) (k_B T)^{3/2} / (⟨σv⟩ m_i^{1/2}); after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Milestone.** Inertial confinement: approximating the confinement time by
the time `τ_E = R √(m_i / T)` an ion needs to cross the distance `R` at its
thermal speed, the criterion becomes `n R ≥ 12 T^{3/2} / (E_ch ⟨σv⟩ √m_i)`.
-/
theorem inertial_confinement_nR (p : DTPlasma) (R mi : ℝ) (hmi : 0 < mi)
    (htau : p.tauE = R * Real.sqrt (mi / p.T)) (h : p.SelfHeating) :
    p.n * R ≥ 12 * p.T ^ ((3:ℝ) / 2) / (p.Ech * p.sigmav * Real.sqrt mi) := by sorry

end LawsonCriterion
