-- Prove2me | Theorems.Thm_GoodmanWitten_lower_mass_limit_aluminium
-- name    : GoodmanWitten.lower_mass_limit_aluminium
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:51:39.813396+00:00
-- url     : https://prove2.me/theorems/bd2db91d-6900-46ae-a568-1a08ce4a5a6b
-- title:
--   Lower limit 1–2 GeV on detectable halo-particle masses (aluminium target)
-- statement:
--   Let the halo velocity be $v = 200$ km/s, i.e. $\beta = v/c = 2\times10^{7}/(2.99792458\times10^{10})$, and let the target be aluminium, $A=27$, with nuclear mass $M = 27\,m_N$. Let the detector threshold $\epsilon$ (in GeV) satisfy
--   $$
--   50\ \mathrm{eV} \le \epsilon \le 100\ \mathrm{eV}.
--   $$
--   Then there is a mass $m_{\min}$ with $1\ \mathrm{GeV} \le m_{\min} \le 2\ \mathrm{GeV}$ such that, for every $m>0$,
--   $$
--   \frac{(2m\beta)^2}{2M} \ge \epsilon \iff m \ge m_{\min}.
--   $$
--   That is, a halo particle can deposit the threshold energy only if its mass is at least $m_{\min}\in[1,2]$ GeV.
--
--   This is the paper's lower limit on the mass of detectable halo particles.
--
--   **Formalization Note** Energies are in GeV, so $50$ eV is written `50e-9`.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3059, right column, paragraph 2

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem lower_mass_limit_aluminium (ε : ℝ) (hε₁ : 50e-9 ≤ ε) (hε₂ : ε ≤ 100e-9) :
    ∃ mmin : ℝ, 1 ≤ mmin ∧ mmin ≤ 2 ∧
      ∀ m : ℝ, 0 < m →
        (ε ≤ maxRecoilEnergy m (nucleusMass 27) (2e7 / speedOfLight) ↔ mmin ≤ m) := by sorry

end GoodmanWitten
