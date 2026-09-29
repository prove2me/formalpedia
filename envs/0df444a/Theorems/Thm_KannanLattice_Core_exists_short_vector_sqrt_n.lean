-- Prove2me | Theorems.Thm_KannanLattice_Core_exists_short_vector_sqrt_n
-- name    : KannanLattice.Core.exists_short_vector_sqrt_n
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:12:23.69425+00:00
-- url     : https://prove2.me/theorems/722e4887-de7f-467f-beef-dd9ddcbe5c03
-- title:
--   Theorem (1.12) — a nonzero lattice vector of length ≤ √n·d(L)^{1/n} (constant √n; the printed ½√n fails for n ≤ 7)
-- statement:
--   Let $b_1,\dots,b_m$ be linearly independent vectors of $\mathcal R^k$ with $m\ge 1$, let $L=L(b_1,\dots,b_m)$ be the $m$-dimensional lattice they generate, and let $d(L)=\prod_{t=1}^m|b_t^*|$ be its determinant. Then there is a nonzero $v\in L$ with
--
--   $$|v|\le \sqrt m\,\big(d(L)\big)^{1/m}.$$
--
--   This is the form of Minkowski's theorem that the paper uses throughout: it bounds $\Lambda_1(L)$ by the determinant, and it is applied to the projected lattices $L_i$ (which are not full-dimensional in $\mathcal R^k$) in the proofs of Proposition 4.3 and Theorem (5.5).
--
--   **Formalization Note** The paper prints the constant $\tfrac12\sqrt n$. That constant is false for $n\le 7$: for $n=1$ and $L=d\mathbb Z$ the shortest vector has length $d>d/2$, and for the hexagonal lattice with minimum $1$ one has $d=\sqrt3/2$ and $\tfrac12\sqrt2\,(\sqrt3/2)^{1/2}\approx 0.658<1$ (in general the printed claim is $\gamma_n\le n/4$ for Hermite's constant, false for $2\le n\le7$). The paper's proof breaks at "So the volume of $T$ is greater than $2^n d(L)$", and the paper's own later uses apply the bound with $\sqrt n$ (proof of Proposition 4.3, p. 24). The statement here uses $\sqrt m$. It is stated for an $m$-dimensional lattice in $\mathcal R^k$ with $k\ge m$ arbitrary; $m\ge1$ excludes the zero lattice.
-- source:
--   Kannan, Minkowski's Convex Body Theorem and Integer Programming, Math. Oper. Res. 12 (1987); author's final manuscript (CMU-CS-96-105), p. 9, Theorem (1.12) (constant corrected from ½√n to √n)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- Theorem (1.12) of Kannan (1987), p. 9, with the constant corrected from `½√m` to `√m`:
every `m`-dimensional lattice `L(b)` in `ℝᵏ` (`m ≥ 1`, `b` linearly independent) has a nonzero
vector of length at most `√m · d(L)^{1/m}`. -/
theorem exists_short_vector_sqrt_n (m k : ℕ) (hm : 1 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ v ∈ lattice b, v ≠ 0 ∧
      ‖v‖ ≤ Real.sqrt m * latticeDet b ^ ((1 : ℝ) / m) := by sorry

end KannanLattice.Core
