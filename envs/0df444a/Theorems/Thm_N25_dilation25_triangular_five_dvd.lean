-- Prove2me | Theorems.Thm_N25_dilation25_triangular_five_dvd
-- name    : N25.dilation25_triangular_five_dvd
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:11.49747+00:00
-- url     : https://prove2.me/theorems/e1c88a03-1734-4576-824f-c264e6637258
-- title:
--   A non-width-one factorization forces divisibility by $5$
-- statement:
--   Let $A,B\in\mathrm{SL}_2(\mathbb Z)$, let $d\in\mathbb N$ and $e,v\in\mathbb Z$, assume $d>0$, $e>0$, $de=25$, and
--
--   $$\begin{pmatrix}25&0\0&1\end{pmatrix}A=B\begin{pmatrix}d&v\0&e\end{pmatrix}.$$
--
--   If $25$ does not divide the lower-left entry $A_{21}$, then $5$ divides the upper-left entry $B_{11}$. This is the arithmetic constraint needed to isolate the middle and width-$25$ cusp cases.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Matrix

theorem N25.dilation25_triangular_five_dvd
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : ℕ) (e v : ℤ)
    (hd : 0 < d) (he : 0 < e) (hde : (d : ℤ) * e = 25)
    (hm : !![25, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) ℤ) =
      (B : Matrix (Fin 2) (Fin 2) ℤ) * !![(d : ℤ), v; 0, e])
    (hA : ¬ (25 : ℤ) ∣ A 1 0) : (5 : ℤ) ∣ B 0 0 := by sorry
