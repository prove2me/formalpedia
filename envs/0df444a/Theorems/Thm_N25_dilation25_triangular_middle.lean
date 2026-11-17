-- Prove2me | Theorems.Thm_N25_dilation25_triangular_middle
-- name    : N25.dilation25_triangular_middle
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:13.857841+00:00
-- url     : https://prove2.me/theorems/0d782935-4a99-473d-a972-7a150c725091
-- title:
--   The middle triangular case has diagonal entries $5$
-- statement:
--   Let $A,B\in\mathrm{SL}_2(\mathbb Z)$, let $d\in\mathbb N$ and $e,v\in\mathbb Z$, assume $e>0$, $de=25$, and
--
--   $$\begin{pmatrix}25&0\0&1\end{pmatrix}A=B\begin{pmatrix}d&v\0&e\end{pmatrix}.$$
--
--   If $5\mid A_{21}$ but $25\nmid A_{21}$, then $d=e=5$ and $5\nmid v$. This determines the precise triangular data for a width-$5$ cusp.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Matrix

theorem N25.dilation25_triangular_middle
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : ℕ) (e v : ℤ)
    (he : 0 < e) (hde : (d : ℤ) * e = 25)
    (hm : !![25, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) ℤ) =
      (B : Matrix (Fin 2) (Fin 2) ℤ) * !![(d : ℤ), v; 0, e])
    (hA5 : (5 : ℤ) ∣ A 1 0) (hA25 : ¬ (25 : ℤ) ∣ A 1 0) :
    d = 5 ∧ e = 5 ∧ ¬ (5 : ℤ) ∣ v := by sorry
