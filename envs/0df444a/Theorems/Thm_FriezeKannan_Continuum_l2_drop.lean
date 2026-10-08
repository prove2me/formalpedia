-- Prove2me | Theorems.Thm_FriezeKannan_Continuum_l2_drop
-- name    : FriezeKannan.Continuum.l2_drop
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:03.254984+00:00
-- url     : https://prove2.me/theorems/fd1cd613-c5be-484c-8daa-5248be85278e
-- title:
--   §8, proof of Theorem 12, p. 217 — ‖w − CUT(S,T,d)‖²₂ − ‖w‖²₂ = −|S||T|d² = −w(S,T)²/(|S||T|) for d = w(S,T)/(|S||T|)
-- statement:
--   Let $w$ be a square-integrable real function on $[0,1]^2$, and let $S,T\subseteq[0,1]$ be measurable sets with $|S|\,|T|>0$, where $|S|$ is the Lebesgue measure of $S$. Put
--   $$d=\frac{w(S,T)}{|S|\,|T|},\qquad w(S,T)=\int_{S\times T}w(x,y)\,dx\,dy,$$
--   and let $w'=w-\mathrm{CUT}(S,T,d)$ be $w$ with the cut function of value $d$ on $S\times T$ subtracted. Then
--   $$\|w'\|_2^2-\|w\|_2^2=\int_{S\times T}\big((w(x,y)-d)^2-w(x,y)^2\big)\,dx\,dy=-|S|\,|T|\,d^2=-\frac{w(S,T)^2}{|S|\,|T|}.$$
--
--   This is the computation at the heart of the proof of Theorem 12: subtracting the best constant on a rectangle lowers the squared $L^2$ norm by exactly $w(S,T)^2/(|S||T|)$.
--
--   **Formalization Note.** $|S|\,|T|>0$ is not written on the page, where it follows from $|w_t(S,T)|>\epsilon\|f\|_2$; it is assumed here because $d$ divides by $|S|\,|T|$. Square integrability of $w$ (Mathlib's `MemLp w 2`) is the page's standing assumption $\|w\|_2<\infty$; without it Lean's integrals default to $0$.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 217, §8, proof of Theorem 12 (the three equalities of the displayed computation)

import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory

namespace FriezeKannan.Continuum

theorem l2_drop (w : Sq → ℝ) (hw : MemLp w 2) (S T : Set unitInterval)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hpos : 0 < (volume S).toReal * (volume T).toReal) :
    let d := rectInt w S T / ((volume S).toReal * (volume T).toReal)
    (l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2
        = ∫ p in S ×ˢ T, ((w p - d) ^ 2 - w p ^ 2)) ∧
    (l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2
        = -((volume S).toReal * (volume T).toReal) * d ^ 2) ∧
    (l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2
        = -(rectInt w S T) ^ 2 / ((volume S).toReal * (volume T).toReal)) := by sorry

end FriezeKannan.Continuum
