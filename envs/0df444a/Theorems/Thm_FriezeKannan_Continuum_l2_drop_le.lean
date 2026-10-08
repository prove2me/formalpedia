-- Prove2me | Theorems.Thm_FriezeKannan_Continuum_l2_drop_le
-- name    : FriezeKannan.Continuum.l2_drop_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:05.183406+00:00
-- url     : https://prove2.me/theorems/795d54ec-cee7-4202-8f13-714b709004d1
-- title:
--   §8, proof of Theorem 12, p. 217 — if |w(S,T)| > ε‖f‖₂ then subtracting CUT(S,T,d) lowers ‖w‖²₂ by at least ε²‖f‖²₂
-- statement:
--   Let $f$ and $w$ be real functions on $[0,1]^2$ with $w$ square integrable, let $\epsilon>0$, and let $S,T\subseteq[0,1]$ be measurable sets with
--   $$|w(S,T)|>\epsilon\|f\|_2 .$$
--   Put $d=w(S,T)/(|S|\,|T|)$, where $|S|$ is the Lebesgue measure of $S$. Then
--   $$\|w-\mathrm{CUT}(S,T,d)\|_2^2-\|w\|_2^2\le-\epsilon^2\|f\|_2^2 .$$
--
--   In the proof of Theorem 12, $w=w_t$ is the current error and $f$ the function being decomposed; each new cut function lowers the squared error by at least $\epsilon^2\|f\|_2^2$, which bounds the number of steps by $1/\epsilon^2$.
--
--   **Formalization Note.** $\epsilon>0$ is the paper's implicit range of the error parameter. No positivity of $|S|\,|T|$ is assumed: it follows from the hypothesis, since $w(S,T)=0$ when $|S|\,|T|=0$. No hypothesis on $f$ is needed beyond what $\|f\|_2$ means; $\|f\|_2$ is the square root of $\int f^2$.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 217, §8, proof of Theorem 12 (final inequality of the displayed computation)

import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory

namespace FriezeKannan.Continuum

theorem l2_drop_le (f w : Sq → ℝ) (hw : MemLp w 2) (ε : ℝ) (hε : 0 < ε)
    (S T : Set unitInterval) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h : ε * l2Norm f < |rectInt w S T|) :
    let d := rectInt w S T / ((volume S).toReal * (volume T).toReal)
    l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2 ≤ -ε ^ 2 * l2Norm f ^ 2 := by sorry

end FriezeKannan.Continuum
