-- Prove2me | Theorems.Thm_KarpPapadimitriou_SmallFacial_cramer_bound
-- name    : KarpPapadimitriou.SmallFacial.cramer_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:40:39.231141+00:00
-- url     : https://prove2.me/theorems/f7ca0bf0-d651-4b4c-b7e1-11865631aadb
-- title:
--   Cramer's-rule coefficient bound for a supporting inequality
-- statement:
--   Let $n\ge1$ and $x\ge1$. Suppose an integral $(n-1)\times n$ matrix $W$ has linearly independent rows, each entry of absolute value at most $2x$, and an integral vector $v_0$ has entries of absolute value at most $x$. There is a nonzero integral normal $f$ satisfying $Wf=0$. Its coordinates and the intercept $g=f\cdot v_0$ obey
--   $$|f_i|\le(2nx)^n,\qquad |g|\le(2nx)^n.$$
--   This is the coefficient estimate used at the end of the proof of Lemma 1.
--
--   **Formalization Note** The paper's rows $v_i-v_0$ can have magnitude $2x$, so that is the bound on entries of $W$. The positive hypotheses on $n$ and $x$ cover the degenerate determinant case; the bound remains the paper's $(2nx)^n$.
-- source:
--   Karp & Papadimitriou, MIT/LCS/TM-154 (Feb. 1980), pp. 6–7, proof of Lemma 1, Cramer's-rule normal and final coefficient bound; https://dspace.mit.edu/server/api/core/bitstreams/eb122126-c312-4445-a8d2-153e3e7d285f/content

import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP

namespace KarpPapadimitriou.SmallFacial

/-- pp. 6–7, proof of Lemma 1: bounded integral normals from `n-1` independent rows. -/
theorem cramer_bound (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x)
    (W : Matrix (Fin (n - 1)) (Fin n) ℤ) (v₀ : Fin n → ℤ)
    (hW : LinearIndependent ℚ (fun i : Fin (n - 1) => fun j : Fin n => (W i j : ℚ)))
    (hWb : ∀ i j, (W i j).natAbs ≤ 2 * x)
    (hv : ∀ j, (v₀ j).natAbs ≤ x) :
    ∃ f : Fin n → ℤ,
      f ≠ 0 ∧
      (∀ i, (∑ j, W i j * f j) = 0) ∧
      (∀ j, (f j).natAbs ≤ (2 * n * x) ^ n) ∧
      (∑ j, f j * v₀ j).natAbs ≤ (2 * n * x) ^ n := by sorry

end KarpPapadimitriou.SmallFacial
