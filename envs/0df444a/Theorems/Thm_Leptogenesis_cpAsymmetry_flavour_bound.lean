-- Prove2me | Theorems.Thm_Leptogenesis_cpAsymmetry_flavour_bound
-- name    : Leptogenesis.cpAsymmetry_flavour_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:09:54.386823+00:00
-- url     : https://prove2.me/theorems/48d6e815-8295-4f47-a999-d2943263bfe0
-- title:
--   Upper bound on the flavoured CP asymmetry $|\varepsilon_{\alpha\alpha}|\le\frac{3M_1m_{\max}}{16\pi v_u^2}\sqrt{B_{\phi\ell_\alpha}+B_{\bar\phi\bar\ell_\alpha}}$ (Eq. 5.10)
-- statement:
--   Let $v_u>0$, $M_1,M_2,M_3>0$, $\lambda$ a complex $3\times3$ Yukawa matrix, and let $[m]=U^*D_mU^\dagger$ be a diagonalization (Eq. (2.6)) of the light-neutrino mass matrix $[m]$ of Eq. (2.5), with $U$ unitary and $m_i\ge0$; let $m_{\max}=\max_im_i$. Then for every flavour $\alpha$, the CP asymmetry of Eq. (5.9) satisfies Eq. (5.10): $$|\varepsilon_{\alpha\alpha}|\le\frac{3M_1m_{\max}}{16\pi v_u^2}\sqrt{B^{N_1}_{\phi\ell_\alpha}+B^{N_1}_{\bar\phi\bar\ell_\alpha}},$$ with the tree-level branching ratios $B^{N_1}_{\phi\ell_\alpha}+B^{N_1}_{\bar\phi\bar\ell_\alpha}=\Gamma_{\alpha\alpha}/\Gamma_D=|\lambda_{\alpha1}|^2/[\lambda^\dagger\lambda]_{11}$ (Eq. (4.5)).
-- source:
--   S. Davidson, E. Nardi, Y. Nir, Leptogenesis, Physics Reports 466 (2008) 105–177, https://doi.org/10.1016/j.physrep.2008.06.002, Sec. 5.2, Eq. (5.10) (p. 122), with Eqs. (2.5), (2.6), (4.5), (5.9)

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

open Matrix

namespace Leptogenesis

/-- Eq. (5.10): upper bound on the flavoured CP asymmetry,
`|ε_{αα}| ≤ 3 M₁ m_max / (16 π v_u²) · √(B_{φℓ_α} + B_{φ̄ℓ̄_α})`,
with the tree-level branching ratio `B_{φℓ_α} + B_{φ̄ℓ̄_α} = Γ_{αα} / Γ_D`. -/
theorem cpAsymmetry_flavour_bound (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ) (hM : ∀ k, 0 < M k)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses) (α : Fin 3) :
    |cpAsymmetry v M lam α| ≤
      3 * M 0 * (⨆ i, masses i) / (16 * Real.pi * v ^ 2) *
        Real.sqrt (partialDecayRate M lam α / totalDecayRate M lam) := by sorry

end Leptogenesis
