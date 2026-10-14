-- Prove2me | Theorems.Thm_GoodmanWitten_detectability
-- name    : GoodmanWitten.detectability
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:58:53.321766+00:00
-- url     : https://prove2.me/theorems/b0d30060-4bbb-4ab7-8527-8214f1def948
-- title:
--   Goodman–Witten detectability of coherent, spin-dependent and strongly interacting dark matter
-- statement:
--   Take the standard halo parameters $\rho = 10^{-24}$ g/cm$^3$ and $v = 200$ km/s, and the detector sensitivity of 1 event per kg per day. Then the three detectability claims of Goodman–Witten hold for the rate formula $R = KF\sigma$:
--
--   1. **Coherent weak interactions (lead).** For a lead target ($A = 207$, $N = 125$, $Z = 82$, $M = 207\,m_N$), with $\bar Y = 1$, $\bar N = N-(1-4\sin^2\theta)Z$ and any weak mixing angle $0.2\le\sin^2\theta\le0.25$, the rate from the coherent cross section of Eq. (2) satisfies
--   $$
--   R \ge 1\ \text{event/kg/day}\qquad\text{for all } 1\ \mathrm{GeV}\le m\le 10^7\ \mathrm{GeV}.
--   $$
--   2. **Spin-dependent interactions (photinos).** For every target $A>0$, with photino mass equal to the nuclear mass and $\lambda^2J(J+1) = 1$, in both cases $(q, M_{\tilde Q}) = (\tfrac23e, 100\ \mathrm{GeV})$ and $(\tfrac13e, 50\ \mathrm{GeV})$ the rate is of order 1:
--   $$
--   1 \le R < 10\ \text{events/kg/day}.
--   $$
--   3. **Strongly interacting particles.** For every target with $27\le A\le207$ (from aluminium to lead) and stopping factor $\epsilon = 1$, there is a mass $M^*$ with
--   $$
--   1.5\times10^{13}\ \mathrm{GeV}\le M^*\le 4.5\times10^{13}\ \mathrm{GeV}
--   $$
--   such that $R\ge1$ event/kg/day exactly when $M_X\le M^*$; i.e. such particles are detectable up to $2$–$4\times10^{13}$ GeV.
--
--   These are the quantitative conclusions behind the paper's abstract: a detector sensitive to 1 event/kg day probes the three classes of candidates over wide mass ranges.
--
--   **Formalization Note** Item 1 uses Eq. (2), which ignores the finite size of the nucleus (as in the paper's sentence); the mixing angle is quantified over $[0.2, 0.25]$ because the paper does not fix it. "Of order 1" is read as $1\le R<10$ and "$\lambda^2J(J+1)\sim1$, masses comparable" as exact equalities. "$2$–$4\times10^{13}$" is read to one significant figure as $[1.5, 4.5]\times10^{13}$.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3060 (coherent: 'For a target such as lead, the event rate is at least 1/kg day for m <~ 10^7 GeV'), p. 3061 (spin-dependent: 'an event rate of order 1/kg day arises for q = 2/3 e, M = 100 GeV, or q = 1/3 e, M = 50 GeV, assuming lambda^2 J(J+1) ~ 1'), p. 3062 (strong: 'strongly interacting dark-matter candidates are detectable at masses up to 2-4 x 10^13 GeV')

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem detectability :
    (∀ s m : ℝ, 0.2 ≤ s → s ≤ 0.25 → 1 ≤ m → m ≤ 1e7 →
      1 ≤ eventRatePerKgDay 207
        (coherentCrossSection m (nucleusMass 207) 1 (effectiveNeutronNumber 125 82 s))
        1e-24 2e7 m) ∧
    (∀ A Q MQ : ℝ, 0 < A → (Q = 2 / 3 ∧ MQ = 100 ∨ Q = 1 / 3 ∧ MQ = 50) →
      1 ≤ eventRatePerKgDay A (photinoCrossSection (nucleusMass A) (nucleusMass A) Q MQ 1)
          1e-24 2e7 (nucleusMass A) ∧
        eventRatePerKgDay A (photinoCrossSection (nucleusMass A) (nucleusMass A) Q MQ 1)
          1e-24 2e7 (nucleusMass A) < 10) ∧
    (∀ A : ℝ, 27 ≤ A → A ≤ 207 →
      ∃ Mstar : ℝ, 1.5e13 ≤ Mstar ∧ Mstar ≤ 4.5e13 ∧
        ∀ MX : ℝ, 0 < MX → (1 ≤ strongEventRate A MX 1 1e-24 2e7 ↔ MX ≤ Mstar)) := by sorry

end GoodmanWitten
