-- Prove2me | Theorems.Thm_N25_siegelIndex25_nontrivial
-- name    : N25.siegelIndex25_nontrivial
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:03.64276+00:00
-- url     : https://prove2.me/theorems/cffb4098-1a74-4602-87c0-de0ab0508603
-- title:
--   A primitive Siegel index cannot vanish in both transformed coordinates
-- statement:
--   Let $B=\begin{pmatrix}a&b\c&d\end{pmatrix}∈SL_2(ℤ)$ and let $g∈ℤ$ with $25∤g$. If $25∣ga$, then $$25∤gb.$$ This guarantees that the transformed level-$25$ Siegel index remains nontrivial.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem N25.siegelIndex25_nontrivial (B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (g : ℤ) (hg : ¬(25 : ℤ) ∣ g) :
    (25 : ℤ) ∣ g * B 0 0 → ¬(25 : ℤ) ∣ g * B 0 1 := by sorry
