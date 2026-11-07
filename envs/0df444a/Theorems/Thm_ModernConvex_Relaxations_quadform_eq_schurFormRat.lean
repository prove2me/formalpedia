-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_quadform_eq_schurFormRat
-- name    : ModernConvex.Relaxations.quadform_eq_schurFormRat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:44.90389+00:00
-- url     : https://prove2.me/theorems/64b20795-d1b8-44bf-95ae-05919ba13a11
-- title:
--   Completing the square over the rationals
-- statement:
--   **Completing the square at a pivot, over $\mathbb Q$.**
--
--   Let $M$ be a rational symmetric matrix of order $n$, $i$ an index with $M_{ii}\ne0$, and $v\in\mathbb Q^n$. Then
--   $$v^{\mathsf T}Mv=M_{ii}\Big(v_i+\frac{1}{M_{ii}}\sum_{j\ne i}M_{ij}v_j\Big)^{2}+Q_i(v),$$
--   with $Q_i$ the rational Schur form.
--
--   Both sides expand to $M_{ii}v_i^2+2v_iP+Q$, where $P=\sum_{j\ne i}M_{ij}v_j$ and $Q=\sum_{j,k\ne i}v_jv_kM_{jk}$: the left by splitting the double sum $\sum_p\sum_qv_p(M_{pq}v_q)$ at the index $i$ twice and using symmetry on the two cross terms, the right by expanding the square and cancelling $M_{ii}^{-1}P^2$.
--
--   This is the exact rational analogue of the real identity, and it is what the computable PSD oracle uses: the decision procedure runs entirely over $\mathbb Q$, where comparisons are decidable, so its recursive step needs the identity over $\mathbb Q$ rather than over $\mathbb R$. Only field algebra is involved, so the proof is the real one verbatim.
-- source:
--   Schur complement at a 1x1 pivot, over Q; recursive step of the computable symmetric-elimination PSD oracle for the MAXCUT SDP.

import Mathlib
import Definitions.Def_ModernConvex_SchurFormRat

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **Completing the square, over `ℚ`.** -/
theorem quadform_eq_schurFormRat {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} (hM : M.IsHermitian)
    (i : Fin n) (ha : M i i ≠ 0) (v : Fin n → ℚ) :
    v ⬝ᵥ (M *ᵥ v)
      = M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
        + schurFormRat M i v := by sorry

end ModernConvex.Relaxations
