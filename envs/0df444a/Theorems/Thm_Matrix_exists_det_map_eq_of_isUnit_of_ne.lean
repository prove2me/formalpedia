-- Prove2me | Theorems.Thm_Matrix_exists_det_map_eq_of_isUnit_of_ne
-- name    : Matrix.exists_det_map_eq_of_isUnit_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/7495ac1f-64db-59f3-a891-f340faa0331c
-- title:
--   Prescribing determinants mod two distinct primes
-- statement:
--   Let $\ell$ and $q$ be prime natural numbers with $\ell \neq q$, let $u$ be a unit of $\mathbb{Z}/\ell\mathbb{Z}$ and let $v$ be a unit of $\mathbb{Z}/q\mathbb{Z}$. The assertion is that there exists a $2 \times 2$ matrix $g$ with integer entries such that three conditions hold: first, the determinant of the matrix obtained by reducing each entry of $g$ along the ring homomorphism $\mathbb{Z} \to \mathbb{Z}/q\ell\mathbb{Z}$ is a unit of $\mathbb{Z}/q\ell\mathbb{Z}$; second, the image of the integer $\det g$ in $\mathbb{Z}/\ell\mathbb{Z}$ equals the image of $u$ under the inclusion of units into $\mathbb{Z}/\ell\mathbb{Z}$; and third, the image of $\det g$ in $\mathbb{Z}/q\mathbb{Z}$ equals the image of $v$. Thus every prescribed pair of residual determinant classes at two distinct primes is realised by a single integral matrix whose reduction modulo the product is invertible.
--
--   This is the elementary statement that the determinant map $\mathrm{GL}_2(\mathbb{Z}/q\ell\mathbb{Z}) \to (\mathbb{Z}/\ell\mathbb{Z})^\times \times (\mathbb{Z}/q\mathbb{Z})^\times$ is hit by integral matrices, used to produce representatives for the determinant classes indexing components at full level; it is cited in the analysis of the minimal primes and of the $\Gamma_0$-power orbits on the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_det_map_eq_of_isUnit_of_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_det_map_eq_of_isUnit_of_ne
    (ℓ q : ℕ) [Fact ℓ.Prime] [Fact q.Prime] (hℓq : ℓ ≠ q) (u : (ZMod ℓ)ˣ) (v : (ZMod q)ˣ) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det ∧
      ((g.det : ℤ) : ZMod ℓ) = (u : ZMod ℓ) ∧ ((g.det : ℤ) : ZMod q) = (v : ZMod q) := by sorry
