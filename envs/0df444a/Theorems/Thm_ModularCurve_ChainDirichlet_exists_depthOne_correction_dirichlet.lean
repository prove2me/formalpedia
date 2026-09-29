-- Prove2me | Theorems.Thm_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet
-- name    : ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/f5a00886-e3b3-5bf8-b4f6-2365cc015c22
-- title:
--   Simultaneous chain Dirichlet problems after a depth-one correction
-- statement:
--   Let $\iota$ be a finite type, let $n \colon \iota \to \mathbb{N}$ satisfy $1 \le n_i$ for every $i$, and let $r \colon \iota \to \mathbb{N} \to \mathbb{Z}$ be an arbitrary family of integer sequences. The assertion is that there exist a family of integers $\nu \colon \iota \to \mathbb{Z}$ and a family of integer sequences $c \colon \iota \to \mathbb{N} \to \mathbb{Z}$ with the following four properties: (i) $\nu_i = 0$ for every $i$ with $n_i = 1$; (ii) $c_i(0) = 0$ for every $i$; (iii) $c_i(d) = 0$ whenever $n_i \le d$; and (iv) for every $i$ and every $d$ with $1 \le d$ and $d + 1 \le n_i$,
--   $$c_i(d-1) - 2c_i(d) + c_i(d+1) = -\bigl(r_i(d) - \nu_i\bigr) \text{ if } d = 1, \qquad c_i(d-1) - 2c_i(d) + c_i(d+1) = -r_i(d) \text{ otherwise},$$
--   the subtraction $d-1$ being in $\mathbb{N}$ (harmless, as $d \ge 1$). Thus on each chain $0,1,\dots,n_i$ the second difference of $c_i$ is prescribed to be minus the given datum at all interior indices, subject to the vanishing of $c_i$ at both ends, at the cost of altering the datum at the single index $d = 1$ by the correction $\nu_i$; no compatibility whatsoever is imposed on $r$, and the correction is forced to vanish for chains of length one, where there are no interior equations.
--
--   This is the simultaneous solvability of discrete Dirichlet problems with zero boundary values on a finite family of chains of arbitrary lengths, the obstruction being absorbed by a single correction term at the first interior index of each chain. It is used in the construction of inertia-stable twist data on annuli in the place-specialisation arguments, being cited by [`ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus`](thm.html#ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus) and [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedGood_isTwistOf_sub_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedGood_isTwistOf_sub_of_inertiaStable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet {ι : Type*} [Finite ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i)
    (r : ι → ℕ → ℤ) :
    ∃ (ν : ι → ℤ) (c : ι → ℕ → ℤ),
      (∀ i, n i = 1 → ν i = 0) ∧ (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = 0) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i →
        c i (d - 1) - 2 * c i d + c i (d + 1) = -(if d = 1 then r i d - ν i else r i d) := by sorry
