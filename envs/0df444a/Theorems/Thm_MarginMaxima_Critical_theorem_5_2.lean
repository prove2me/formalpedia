-- Prove2me | Theorems.Thm_MarginMaxima_Critical_theorem_5_2
-- name    : MarginMaxima.Critical.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:17.443328+00:00
-- url     : https://prove2.me/theorems/cadb6f95-adab-4000-9a62-f8c47165cd16
-- title:
--   Theorem 5.2 — $\mathrm{fat}^0_{g_\star}(F^{(d)}_{\max,r})\ge c\,r\ln r$ and $\mathrm{fat}_{g_w}(F^{(d)}_{\max,r})\ge c\,r\ln r$ on unit documents, for $d\ge c\,r\ln r$
-- statement:
--   There are absolute constants $c>0$ and $r_0$ such that for $r\ge r_0$ and $d\ge c\,r\ln r$,
--   $$\mathrm{fat}^0_{g_\star}(F^{(d)}_{\max,r})\ge c\,r\ln r\qquad\text{and}\qquad\mathrm{fat}_{g_w}(F^{(d)}_{\max,r})\ge c\,r\ln r,$$
--   on unit documents and heads of norm at most 1, where $g_\star=63/449$ and $g_w=17/(54\sqrt3)$.
--
--   Differences from the source:
--   - reading: fat ≥ c r ln r on unit documents and heads of norm at most 1 → ∃ m ≥ c r ln r and a shattered x : Fin m → Ball d with ‖x i‖ = 1 for all i (zero witnesses at g⋆; witnesses at g_w), the class being MaxClass d r; reason: 'on unit documents' says the shattered points are unit vectors; a shattered sequence of length m is fat ≥ m
--   - encoding: x ↦ max_{j≤r}⟨u_j, x⟩ on the unit ball of R^d, ∥u_j∥ ≤ 1, labels in {±1} → MaxClass d r: functions on the closed-ball subtype Ball d, ⨆ over j : Fin r of inner ℝ (u j) x, ‖u j‖ ≤ 1; labels Bool read through pm; reason: for r ≥ 1 the supremum over Fin r is the maximum of r reals; pm true = 1, pm false = −1
--   - encoding: r, the number of heads → r : ℕ with 1 ≤ r; reason: the paper's r is a positive integer (§1: exactly r heads)
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 9, Theorem 5.2

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass

open BartlettNN.Margin

namespace MarginMaxima.Critical

theorem theorem_5_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ r0 : ℕ, ∀ r : ℕ, 1 ≤ r → r0 ≤ r → ∀ d : ℕ, c * r * Real.log r ≤ d →
      (∃ m : ℕ, c * r * Real.log r ≤ m ∧ ∃ x : Fin m → Ball d,
        (∀ i, ‖(x i).1‖ = 1) ∧ ZeroShatters (MaxClass d r) gStar x) ∧
      (∃ m : ℕ, c * r * Real.log r ≤ m ∧ ∃ x : Fin m → Ball d,
        (∀ i, ‖(x i).1‖ = 1) ∧ GammaShatters (MaxClass d r) gW x) := by sorry

end MarginMaxima.Critical
