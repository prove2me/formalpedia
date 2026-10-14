-- Prove2me | Theorems.Thm_Maldacena2003_scalar_vertex_time_integral
-- name    : Maldacena2003.scalar_vertex_time_integral
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:51:53.229687+00:00
-- url     : https://prove2.me/theorems/0581f978-2324-4552-957d-18b61ac59dfc
-- title:
--   Eq. (4.4): $\sum_{\rm perm}i\int_{-\infty}^0 d\eta\,k_1^2k_2^2e^{ik_t\eta}+{\rm c.c.} = 4\frac{\sum_{i>j}k_i^2k_j^2}{k_t}$
-- statement:
--   Let $k_1,k_2,k_3>0$ and $k_t=k_1+k_2+k_3$. For $\epsilon>0$, put
--   $$S(\epsilon) = \sum_{\sigma\in S_3} 2\,\mathrm{Re}\Big[\, i\int_{-\infty}^{0} k_{\sigma(1)}^2k_{\sigma(2)}^2\, e^{ik_t\eta}\,e^{\epsilon\eta}\,d\eta\Big],$$
--   the sum over the six permutations of the integral plus its complex conjugate. Then
--   $$\lim_{\epsilon\to0^+} S(\epsilon) = 4\,\frac{k_1^2k_2^2+k_1^2k_3^2+k_2^2k_3^2}{k_t}.$$
--
--   This is the time integral in eq. (4.4). It gives the contribution of the cubic vertex of (3.11) to the three-scalar correlator in de Sitter space. The common prefactor $(2\pi)^3\delta^3(\sum\vec k_i)\frac{1}{\prod(2k_i^3)}\frac{\dot\rho_*^6}{\dot\phi_*^2}$ of both sides is omitted.
--
--   **Formalization Note** The contour prescription $\eta\to\eta+i\epsilon|\eta|$ (the standard interacting vacuum) is implemented by the damping factor $e^{\epsilon\eta}$, followed by $\epsilon\to0^+$. The momenta are indexed by `Fin 3`, and the permutations are `Equiv.Perm (Fin 3)`.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 16, eq. (4.4)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem scalar_vertex_time_integral (k : Fin 3 → ℝ) (hk : ∀ i, 0 < k i) :
    Tendsto
      (fun ε : ℝ => ∑ σ : Equiv.Perm (Fin 3),
        2 * (Complex.I * ∫ η in Set.Iic (0 : ℝ),
          ((k (σ 0) : ℂ) ^ 2 * (k (σ 1) : ℂ) ^ 2)
            * Complex.exp (Complex.I * ((k 0 + k 1 + k 2 : ℝ) : ℂ) * (η : ℂ))
            * (Real.exp (ε * η) : ℂ)).re)
      (𝓝[>] 0)
      (𝓝 (4 * (k 1 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 1 ^ 2)
        / (k 0 + k 1 + k 2))) := by sorry

end Maldacena2003
