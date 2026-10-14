-- Prove2me | Theorems.Thm_Multihoming_Local_footnote15_profit_derivative
-- name    : Multihoming.Local.footnote15_profit_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:25.940984+00:00
-- url     : https://prove2.me/theorems/4d66b7a7-9d92-45df-8570-69b85b99b1a2
-- title:
--   Footnote 15, PDF p. 19 (printed p. 13) — dπ_i/dμ|₀ = (2t − e_j)e_i/(4t²) > 0
-- statement:
--   Let $t>0$, and let $\pi_i(\mu)=p_i^M x_i^M$ be firm $i$'s profit at the candidate prices (16), as a function of the network-effect strength $\mu$. At $\mu=0$,
--
--   $$
--   \frac{d\pi_i}{d\mu}\bigg|_{\mu=0}=\frac{(2t-e_j)\,e_i}{4t^2},
--   $$
--
--   and this is positive when $e_i>0$ and $2t-e_j>0$.
--
--   This is the profit part of Proposition 1: weak network effects raise each firm's equilibrium profit under partial multihoming.
--
--   **Formalization Note** The footnote attaches the value to expression (21), but the printed value is the derivative of the equilibrium profit $p_i^M x_i^M$ with respect to $\mu$; it is formalized as such. The derivative is two-sided (`HasDerivAt`).
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 19 (printed p. 13), footnote 15

import Mathlib
import Definitions.Def_Multihoming_Local_Model

namespace Multihoming.Local

/-- Footnote 15, PDF p. 19: the derivative at `μ = 0` of firm i's profit `π_i = p_i x_i` at the
candidate prices (16) is `(2t − e_j) e_i / (4t²)`, positive when `e_i > 0` and `2t − e_j > 0`. -/
theorem footnote15_profit_derivative (t ei ej : ℝ) (ht : 0 < t) :
    HasDerivAt (fun μ => profitM t μ ei ej) ((2 * t - ej) * ei / (4 * t ^ 2)) 0 ∧
      (0 < ei → ej < 2 * t → 0 < (2 * t - ej) * ei / (4 * t ^ 2)) := by sorry

end Multihoming.Local
