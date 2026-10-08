-- Prove2me | Theorems.Thm_FriezeKannan_Continuum_theorem_12
-- name    : FriezeKannan.Continuum.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:08.854979+00:00
-- url     : https://prove2.me/theorems/20aed3dd-598e-4906-9801-ae49021f2139
-- title:
--   Theorem 12, p. 217 — f = f₁ + ⋯ + f_s + w with s ≤ 1/ε² cut functions and ‖w‖_C ≤ ε‖f‖₂
-- statement:
--   Let $f:[0,1]^2\to\mathbb R$ be Lebesgue measurable with
--   $$\|f\|_2^2=\int_{[0,1]^2}f(x,y)^2\,dx\,dy<\infty,$$
--   and let $\epsilon>0$. For measurable $S,T\subseteq[0,1]$ write $g(S,T)=\int_{S\times T}g(x,y)\,dx\,dy$, and let $\|g\|_C=\sup_{S,T}|g(S,T)|$ over measurable $S,T$ be the cut norm. A cut function $\mathrm{CUT}(S,T,d)$ is the function equal to $d$ on $S\times T$ and $0$ elsewhere, for measurable $S,T$ and real $d$.
--
--   **Theorem 12.** There exist cut functions $f_1,\dots,f_s$ with $s\le 1/\epsilon^2$ such that the error $w_s=f-(f_1+\dots+f_s)$ satisfies
--   $$\|w_s\|_C\le\epsilon\|f\|_2. \tag{63}$$
--
--   This is the continuous analogue of the matrix cut decomposition (Theorem 7 of the paper), and the form of weak regularity used for graph limits: every square-integrable kernel on $[0,1]^2$ is, in cut norm, within $\epsilon\|f\|_2$ of a sum of boundedly many rectangle step functions, the number depending on $\epsilon$ alone.
--
--   **Formalization Note.** $[0,1]$ is Mathlib's `unitInterval` with Lebesgue measure; $f$ (Lebesgue) measurable with $\|f\|_2<\infty$ is `MemLp f 2`, which includes almost-everywhere strong measurability, i.e. measurability for the completed Lebesgue measure; no Borel `Measurable f` is required. The cut norm bound is the supremum unfolded: $|w_s(S,T)|\le\epsilon\|f\|_2$ for all measurable $S,T$. The cut functions are indexed by $\{0,\dots,s-1\}$ and must have measurable sets. $\epsilon>0$ is the paper's implicit range of the error parameter (§2.3); for $\epsilon\le0$ the bound $s\le1/\epsilon^2$ is meaningless. The bound $s\le1/\epsilon^2$ is what makes the theorem: without it the statement follows from density of step functions in $L^2$.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 217, Theorem 12 and (63)

import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory

namespace FriezeKannan.Continuum

theorem theorem_12 (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, (s : ℝ) ≤ 1 / ε ^ 2 ∧
      ∃ (Ss Ts : Fin s → Set unitInterval) (d : Fin s → ℝ),
        (∀ t, MeasurableSet (Ss t) ∧ MeasurableSet (Ts t)) ∧
        ∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
          |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f := by sorry

end FriezeKannan.Continuum
