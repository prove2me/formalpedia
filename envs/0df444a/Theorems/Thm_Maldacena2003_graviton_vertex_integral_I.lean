-- Prove2me | Theorems.Thm_Maldacena2003_graviton_vertex_integral_I
-- name    : Maldacena2003.graviton_vertex_integral_I
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:54:29.909583+00:00
-- url     : https://prove2.me/theorems/f9bbfdf3-00ce-40f2-aa7b-4effca4f493f
-- title:
--   Eq. (4.11): $\mathrm{Re}\big[-\int_{-\infty}^0 i\frac{d\eta}{\eta^2}\prod_j(1-ik_j\eta)e^{ik_t\eta}\big] = -k_t+\frac{\sum_{i>j}k_ik_j}{k_t}+\frac{k_1k_2k_3}{k_t^2}$
-- statement:
--   Let $k_1,k_2,k_3>0$ and $k_t = k_1+k_2+k_3$. For a cutoff $\eta_0<0$ and $\epsilon>0$, consider
--   $$J_\epsilon(\eta_0) = \mathrm{Re}\Big[-\,i\int_{-\infty}^{\eta_0}\frac{(1-ik_1\eta)(1-ik_2\eta)(1-ik_3\eta)}{\eta^2}\,e^{ik_t\eta}\,e^{\epsilon\eta}\,d\eta\Big].$$
--   Then there is a function $J$ such that $J_\epsilon(\eta_0)\to J(\eta_0)$ as $\epsilon\to0^+$ for every $\eta_0<0$, and
--   $$\lim_{\eta_0\to0^-}J(\eta_0) = -k_t + \frac{k_1k_2+k_1k_3+k_2k_3}{k_t} + \frac{k_1k_2k_3}{k_t^2} = I .$$
--
--   This is the integral $I$ of eq. (4.11). It controls the graviton–scalar–scalar correlator (4.10) and the three-graviton correlator (4.15). The integral diverges at $\eta\to0$, but the divergence is purely imaginary, so the real part has a finite limit.
--
--   **Formalization Note** The $i\epsilon$ prescription is the damping factor $e^{\epsilon\eta}$ with $\epsilon\to0^+$. The upper endpoint $0$ is reached as the limit $\eta_0\to0^-$ of the real part.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 18, eq. (4.11) and footnote 17

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem graviton_vertex_integral_I (k₁ k₂ k₃ : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) (h₃ : 0 < k₃) :
    ∃ J : ℝ → ℝ,
      (∀ η₀ : ℝ, η₀ < 0 →
        Tendsto
          (fun ε : ℝ => (-(Complex.I * ∫ η in Set.Iic η₀,
            (1 - Complex.I * (k₁ : ℂ) * (η : ℂ)) * (1 - Complex.I * (k₂ : ℂ) * (η : ℂ))
              * (1 - Complex.I * (k₃ : ℂ) * (η : ℂ))
              * Complex.exp (Complex.I * ((k₁ + k₂ + k₃ : ℝ) : ℂ) * (η : ℂ)) / (η : ℂ) ^ 2
              * (Real.exp (ε * η) : ℂ))).re)
          (𝓝[>] 0) (𝓝 (J η₀))) ∧
      Tendsto J (𝓝[<] 0)
        (𝓝 (-(k₁ + k₂ + k₃) + (k₂ * k₁ + k₃ * k₁ + k₃ * k₂) / (k₁ + k₂ + k₃)
          + k₁ * k₂ * k₃ / (k₁ + k₂ + k₃) ^ 2)) := by sorry

end Maldacena2003
