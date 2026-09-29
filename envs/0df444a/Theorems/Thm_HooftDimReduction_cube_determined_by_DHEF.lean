-- Prove2me | Theorems.Thm_HooftDimReduction_cube_determined_by_DHEF
-- name    : HooftDimReduction.cube_determined_by_DHEF
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T01:18:53.993072+00:00
-- url     : https://prove2.me/theorems/3cc1d3e1-7416-4373-bbd6-4982c0a1d0a7
-- title:
--   Discussion of Fig. 1 (p. 10): on a unit cube, the data at $D,H,E,F$ determine all eight corners
-- statement:
--   Fix $p\in\mathbb N$ and six plaquette rules $g_a,\dots,g_f:(\mathbb Z/p)^4\to\mathbb Z/p$, each such that any three entries determine the fourth uniquely. Consider the unit cube with lowest corner $x\in\mathbb Z^3$ and corners $A=x$, $B=x+e^1$, $D=x+e^2$, $E=x+e^3$, $C=x+e^1+e^2$, $F=x+e^1+e^3$, $H=x+e^2+e^3$, $G=x+e^1+e^2+e^3$. Let $f,f':\mathbb Z^3\to\mathbb Z/p$ both satisfy the six face relations (12a–f):
--   $$g_a(f(A),f(B),f(C),f(D))=0,\quad g_b(f(E),f(F),f(G),f(H))=0,\quad g_c(f(A),f(B),f(F),f(E))=0,$$
--   $$g_d(f(D),f(C),f(G),f(H))=0,\quad g_e(f(A),f(D),f(H),f(E))=0,\quad g_f(f(B),f(C),f(G),f(F))=0 .$$
--   If $f$ and $f'$ agree at $D,H,E,F$, then they agree at all eight corners of the cube.
--
--   This is the local propagation step: four consecutive staircase points carry the data of a whole cube.
-- source:
--   G. 't Hooft, "Dimensional Reduction in Quantum Gravity", essay dedicated to Abdus Salam, Utrecht preprint THU-93/26, arXiv:gr-qc/9310026v2, https://arxiv.org/abs/gr-qc/9310026, pp. 8–10, Fig. 1, eqs. (12a–f), and the paragraph after eq. (14): 'Suppose that in the Figure the data are given at D, H, E and F ... By applying four of the six equations (12) the other data on the cube are determined.'

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

namespace HooftDimReduction

theorem cube_determined_by_DHEF (p : ℕ) (g : Fin 6 → (Fin 4 → ZMod p) → ZMod p)
    (hg : ∀ k, IsPlaquetteRule (g k)) (x : Site) (f f' : Site → ZMod p)
    (hf : ∀ k, g k (fun i => f (plaquette (cubeFace x k).1 (cubeFace x k).2 i)) = 0)
    (hf' : ∀ k, g k (fun i => f' (plaquette (cubeFace x k).1 (cubeFace x k).2 i)) = 0)
    (hD : f (x + e2) = f' (x + e2)) (hH : f (x + e2 + e3) = f' (x + e2 + e3))
    (hE : f (x + e3) = f' (x + e3)) (hF : f (x + e1 + e3) = f' (x + e1 + e3)) :
    ∀ a b c : Fin 2,
      f (x + (((a : ℕ) : ℤ), ((b : ℕ) : ℤ), ((c : ℕ) : ℤ))) =
        f' (x + (((a : ℕ) : ℤ), ((b : ℕ) : ℤ), ((c : ℕ) : ℤ))) := by sorry

end HooftDimReduction
