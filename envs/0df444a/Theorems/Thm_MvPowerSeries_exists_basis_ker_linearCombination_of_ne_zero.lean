-- Prove2me | Theorems.Thm_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero
-- name    : MvPowerSeries.exists_basis_ker_linearCombination_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/395b5db5-b82f-5763-be34-1a5f2257363e
-- title:
--   Syzygies of finitely many series in two variables are free
-- statement:
--   Let $\kappa$ be a field, let $m$ be a natural number, and write $A = \mathrm{MvPowerSeries}\,(\mathrm{Fin}\,2)\,\kappa$ for the ring of formal power series over $\kappa$ in two variables indexed by $\mathrm{Fin}\,2$. Let $f : \mathrm{Fin}\,m \to A$ be a family of $m$ such power series, and assume $f \neq 0$ as a function, i.e. $f_i \neq 0$ for at least one index $i$ (which in particular forces $m \geq 1$). Consider the $A$-linear map $\mathrm{Fintype.linearCombination}\,A\,f$ from $\mathrm{Fin}\,m \to A$ to $A$ sending a tuple $c$ to $\sum_{i} c_i \cdot f_i$; its kernel is the module of relations (syzygies) among the $f_i$. The assertion is that there exist a natural number $r$ and an $A$-basis of this kernel indexed by $\mathrm{Fin}\,r$, such that $r + 1 = m$. Thus the relation module is a free $A$-module, and the equation $r + 1 = m$ pins its rank down to $m - 1$.
--
--   This is the two-variable case of the statement that the first syzygy module of a nonzero family of elements of a two-dimensional regular local ring is free, of rank one less than the number of generators (the shape underlying the Hilbert–Burch description of such relation modules). It is used in the proof of [`IsLocalRing.exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries`](thm.html#IsLocalRing.exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPowerSeries.exists_basis_ker_linearCombination_of_ne_zero
    {κ : Type} [Field κ] {m : ℕ} (f : Fin m → MvPowerSeries (Fin 2) κ) (hf : f ≠ 0) :
    ∃ (r : ℕ) (e : Module.Basis (Fin r) (MvPowerSeries (Fin 2) κ)
        (LinearMap.ker (Fintype.linearCombination (MvPowerSeries (Fin 2) κ) f))), r + 1 = m := by sorry
