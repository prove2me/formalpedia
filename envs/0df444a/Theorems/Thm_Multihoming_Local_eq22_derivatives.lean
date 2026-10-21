-- Prove2me | Theorems.Thm_Multihoming_Local_eq22_derivatives
-- name    : Multihoming.Local.eq22_derivatives
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:31.133675+00:00
-- url     : https://prove2.me/theorems/92425709-9a6d-4611-a815-877bce5cb7e2
-- title:
--   (22), PDF p. 18 (printed p. 12) — ∂m/∂μ|₀ = ((2t−e_i)+(2t−e_j))/(4t²) > 0 and ∂s_i/∂μ|₀ = −(2t−e_i)/(4t²) < 0
-- statement:
--   Let $t>0$, and let $m(\mu)$ and $s_i(\mu)$ be the numbers of multihomers and of singlehomers of good $i$ at the candidate prices (16), as functions of the network-effect strength $\mu$. At $\mu=0$,
--
--   $$
--   \frac{\partial m}{\partial\mu}\bigg|_{\mu=0}=\frac{(2t-e_i)+(2t-e_j)}{4t^2},\qquad
--   \frac{\partial s_i}{\partial\mu}\bigg|_{\mu=0}=-\frac{2t-e_i}{4t^2}.
--   $$
--
--   If moreover $2t-e_i>0$ and $2t-e_j>0$ (necessary for partial multihoming at $\mu=0$), the first derivative is positive and the second negative: weak network effects raise the number of multihomers and lower the number of singlehomers.
--
--   **Formalization Note** The page prints the second derivative as $-(2t-e_i)/(2t^2)$; the constant $2t^2$ is a slip, and the value implied by (16), (17) and (19) is $-(2t-e_i)/(4t^2)$. The statement uses the corrected constant; the sign, which is what the paper uses, is unaffected. The derivatives are two-sided (Mathlib's `HasDerivAt`): all functions involved are smooth near $\mu=0$ when $t>0$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 18 (printed p. 12), (22); sign condition PDF p. 19 (printed p. 13)

import Mathlib
import Definitions.Def_Multihoming_Local_Model

namespace Multihoming.Local

/-- (22), PDF p. 18: the derivatives at `μ = 0` of the multihomers `m` and of the singlehomers
`s_i` at the candidate prices (16), and their signs when `2t − e_i > 0` and `2t − e_j > 0`.
The printed constant `2t²` of the second derivative is a slip; the true value is `4t²`. -/
theorem eq22_derivatives (t ei ej : ℝ) (ht : 0 < t) :
    HasDerivAt (fun μ => multiM t μ ei ej) (((2 * t - ei) + (2 * t - ej)) / (4 * t ^ 2)) 0 ∧
      HasDerivAt (fun μ => singleM t μ ei ej) (-(2 * t - ei) / (4 * t ^ 2)) 0 ∧
      (ei < 2 * t → ej < 2 * t →
        0 < ((2 * t - ei) + (2 * t - ej)) / (4 * t ^ 2) ∧ -(2 * t - ei) / (4 * t ^ 2) < 0) := by sorry

end Multihoming.Local
