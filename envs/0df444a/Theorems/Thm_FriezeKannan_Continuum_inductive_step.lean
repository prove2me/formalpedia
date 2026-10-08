-- Prove2me | Theorems.Thm_FriezeKannan_Continuum_inductive_step
-- name    : FriezeKannan.Continuum.inductive_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:30.669992+00:00
-- url     : https://prove2.me/theorems/4785cde9-bc16-4db4-95df-b9c208190f39
-- title:
--   §8, proof of Theorem 12, p. 217 — if ‖w_t‖²₂ ≤ (1 − ε²t)‖f‖²₂ then (63) holds or one more cut function gives ‖w_{t+1}‖²₂ ≤ (1 − ε²(t+1))‖f‖²₂
-- statement:
--   Let $f$ be a measurable real function on $[0,1]^2$ with $\|f\|_2<\infty$, and let $\epsilon>0$. Suppose $f_j=\mathrm{CUT}(S_j,T_j,d_j)$, $1\le j\le t$, are cut functions with measurable $S_j,T_j\subseteq[0,1]$, and that the error $w_t=f-(f_1+\dots+f_t)$ satisfies
--   $$\|w_t\|_2^2\le(1-\epsilon^2 t)\,\|f\|_2^2 .$$
--   Then one of the following holds:
--
--   1. $|w_t(S,T)|\le\epsilon\|f\|_2$ for all measurable $S,T\subseteq[0,1]$, i.e. $\|w_t\|_C\le\epsilon\|f\|_2$ (inequality (63) with $s=t$);
--   2. there are measurable $S,T\subseteq[0,1]$ and a real $d$ such that
--   $$\|w_t-\mathrm{CUT}(S,T,d)\|_2^2\le\big(1-\epsilon^2(t+1)\big)\,\|f\|_2^2 .$$
--
--   This is the induction of the proof of Theorem 12: as long as the cut norm of the error exceeds $\epsilon\|f\|_2$, one more cut function preserves the invariant with $t$ replaced by $t+1$.
--
--   **Formalization Note.** The family of cut functions is indexed by $\{0,\dots,t-1\}$ (the page's $f_0=0$ is the empty sum). The cut norm bound is the definition $\|w\|_C=\sup_{S,T}|w(S,T)|$ unfolded over measurable $S,T$. $\epsilon>0$ is the paper's implicit range. "$f$ measurable with $\|f\|_2<\infty$" is `MemLp f 2` (which includes almost-everywhere measurability, i.e. Lebesgue measurability).
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 217, §8, proof of Theorem 12 (inductive hypothesis and the case split)

import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory

namespace FriezeKannan.Continuum

theorem inductive_step (f : Sq → ℝ) (hf : MemLp f 2)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (Ss Ts : Fin t → Set unitInterval) (d : Fin t → ℝ)
    (hmS : ∀ j, MeasurableSet (Ss j) ∧ MeasurableSet (Ts j))
    (hinv : l2Norm (fun p => f p - cutFunSum Ss Ts d p) ^ 2
      ≤ (1 - ε ^ 2 * t) * l2Norm f ^ 2) :
    (∀ S T : Set unitInterval, MeasurableSet S → MeasurableSet T →
        |rectInt (fun p => f p - cutFunSum Ss Ts d p) S T| ≤ ε * l2Norm f) ∨
    ∃ (S T : Set unitInterval) (d' : ℝ), MeasurableSet S ∧ MeasurableSet T ∧
      l2Norm (fun p => f p - cutFunSum Ss Ts d p - cutFun S T d' p) ^ 2
        ≤ (1 - ε ^ 2 * (t + 1)) * l2Norm f ^ 2 := by sorry

end FriezeKannan.Continuum
