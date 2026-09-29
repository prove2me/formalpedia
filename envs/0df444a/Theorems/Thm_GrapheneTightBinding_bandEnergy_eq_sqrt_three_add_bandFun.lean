-- Prove2me | Theorems.Thm_GrapheneTightBinding_bandEnergy_eq_sqrt_three_add_bandFun
-- name    : GrapheneTightBinding.bandEnergy_eq_sqrt_three_add_bandFun
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T20:33:55.952986+00:00
-- url     : https://prove2.me/theorems/54c38d95-0912-4d2f-be2f-a9e903c40e40
-- title:
--   Eqs. (13)–(14): $E_+(k)=t\sqrt{3+f(k)}$
-- statement:
--   **The energy bands via $f(k)$ (Eqs. 13–14).** With
--   $$f(k)=2\cos(\sqrt3k_ya)+4\cos\!\left(\frac{3k_xa}{2}\right)\cos\!\left(\frac{\sqrt3k_ya}{2}\right),$$
--   the band energies take the compact form $E_\pm(k)=\pm t\sqrt{3+f(k)}$ for $t\ge0$. This is
--   the form in which graphene's dispersion is usually quoted; it is equivalent to Eq. (12)
--   through the double-angle identity for $\cos(\sqrt3k_ya)$.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem bandEnergy_eq_sqrt_three_add_bandFun (a t : ℝ) (ht : 0 ≤ t) (k : ℝ × ℝ) :
    bandEnergy a t k = t * Real.sqrt (3 + bandFun a k) := by
  sorry

end GrapheneTightBinding
