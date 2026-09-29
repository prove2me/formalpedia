-- Prove2me | Theorems.Thm_Leptogenesis_cpAsymmetry_total_bound
-- name    : Leptogenesis.cpAsymmetry_total_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:09:04.844053+00:00
-- url     : https://prove2.me/theorems/29ec0a16-838e-4f0d-b6f1-ee58ebfb2e3b
-- title:
--   Bound on the total CP asymmetry $|\varepsilon|\le 3M_1(m_{\max}-m_{\min})/(16\pi v_u^2)$ (Sec. 5.2)
-- statement:
--   Let $v_u>0$, $M_k>0$, $\lambda$ a complex $3\times3$ matrix, and $[m]=U^*D_mU^\dagger$ with $U$ unitary and $m_i\ge0$. For the hierarchical-limit flavoured CP asymmetries $\varepsilon_{\alpha\alpha}$ of Eq. (5.9), the total asymmetry $\varepsilon=\sum_\alpha\varepsilon_{\alpha\alpha}$ satisfies $$|\varepsilon|\le\frac{3M_1\,(m_{\max}-m_{\min})}{16\pi v_u^2},$$ where $m_{\max}$ and $m_{\min}$ are the largest and smallest light-neutrino masses (the Davidson–Ibarra bound $3M_1(m_3-m_1)/(16\pi v^2)$ quoted in Sec. 5.2, item 3; the $\beta\to1$ form of Eq. (5.17)).
-- source:
--   S. Davidson, E. Nardi, Y. Nir, Leptogenesis, Physics Reports 466 (2008) 105–177, https://doi.org/10.1016/j.physrep.2008.06.002, Sec. 5.2, item 3 of the list after Eq. (5.12) (p. 123), cf. Eq. (5.17) (p. 123) and refs. [73,74] therein

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

open Matrix

namespace Leptogenesis

/-- Sec. 5.2 (item 3 after Eq. (5.12)); cf. Eq. (5.17): upper bound on the total CP asymmetry,
`|ε| = |∑_α ε_{αα}| ≤ 3 M₁ (m_max − m_min) / (16 π v_u²)`. -/
theorem cpAsymmetry_total_bound (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ) (hM : ∀ k, 0 < M k)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses) :
    |∑ α, cpAsymmetry v M lam α| ≤
      3 * M 0 * ((⨆ i, masses i) - ⨅ i, masses i) / (16 * Real.pi * v ^ 2) := by sorry

end Leptogenesis
