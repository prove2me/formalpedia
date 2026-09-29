-- Prove2me | Theorems.Thm_LawsonCriterion_triple_product_DT_bound
-- name    : LawsonCriterion.triple_product_DT_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:13:56.650623+00:00
-- url     : https://prove2.me/theorems/2fa9bb4b-29b3-4a28-ba3c-fe77aca83fac
-- title:
--   Numerical D-T triple product bound: $nT\tau_E \ge 3 \cdot 10^{21}$ keV s m$^{-3}$
-- statement:
--   Specialising the triple product bound to the deuterium-tritium reaction. Measuring the temperature in keV and the reactivity in $\mathrm{m^3/s}$, the charged fusion product carries $E_{\mathrm{ch}} = 3.5\ \mathrm{MeV} = 3500\ \mathrm{keV}$, and near $T = 14$ keV the Maxwellian average is well approximated by $\langle\sigma v\rangle = 1.1 \cdot 10^{-24}\,T^2\ \mathrm{m^3/s}$ (Wesson, *Tokamaks*, 3rd ed.). With these two substitutions the temperature cancels out of the right-hand side of the triple product bound, and a self-heating D-T plasma must satisfy
--
--   $$n\,T\,\tau_E \;\ge\; 3 \cdot 10^{21}\ \mathrm{keV\,s\,m^{-3}},$$
--
--   the number quoted as the D-T triple product requirement. (The exact value of $12/(3500 \cdot 1.1 \cdot 10^{-24})$ is about $3.12 \cdot 10^{21}$; the statement asserts the rounded bound $3 \cdot 10^{21}$.)
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Extension into the triple product", the reactivity fit ⟨σv⟩ = 1.1·10⁻²⁴ T² m³/s (T in keV) with E_ch = 3.5 MeV, and the resulting value nTτ_E ≥ 3·10²¹ keV s/m³; after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Milestone.** The numerical D-T triple product bound: with the charged
product energy `E_ch = 3500 keV` and the reactivity approximation
`⟨σv⟩ = 1.1 · 10⁻²⁴ T² m³/s` (`T` in keV), self-heating forces
`n T τ_E ≥ 3 · 10²¹ keV s / m³`.
-/
theorem triple_product_DT_bound (p : DTPlasma) (h : p.SelfHeating)
    (hEch : p.Ech = 3500) (hsv : p.sigmav = (11 / 10 ^ 25) * p.T ^ 2) :
    p.n * p.T * p.tauE ≥ 3 * 10 ^ 21 := by sorry

end LawsonCriterion
