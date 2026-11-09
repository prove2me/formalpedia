-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_convex_majorant
-- name    : OnlineCarpoolingLei.Oblivious.convex_majorant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:31.434929+00:00
-- url     : https://prove2.me/theorems/fbcef273-1737-48a6-b753-b37bc87411d5
-- title:
--   Lemma 6.1 — $\Psi_f\in\mathcal C_+$, $\int\Psi_f\,d\gamma\le\int f\,d\gamma$, and $\Psi_f$ majorizes an allowed move
-- statement:
--   Fix an edge $e=\mathbf 1_u-\mathbf 1_v$ on $[n]$ and write $x^\perp=x-\frac12\langle x,e\rangle e$. For $f\in\mathcal C_+$ (finite, nonnegative, convex and $\gamma$-integrable, $\gamma=N(0,50I_n)$) let $g_y(s)=f(y+\frac s2e)$ for $y\in e^\perp$ and put $\Psi_f(x)=\Psi_{g_{x^\perp}}(\langle x,e\rangle)$. Then:
--
--   1. $\Psi_f\in\mathcal C_+$;
--   2. the Gaussian integral does not increase:
--   $$\int\Psi_f\,d\gamma\le\int f\,d\gamma;\tag{6.1}$$
--   3. for every $x\in\mathbb R^n$ there is $q\in B_x$ such that
--   $$q\,f(x+e)+(1-q)\,f(x-e)\le\Psi_f(x).\tag{6.2}$$
--
--   This is the high-dimensional version of Lemma 5.2. Combined with $\mu\preceq_{cx}\gamma$, it shows that for each single test function $f$ some selection in $B$ satisfies the inequality $\int f\,d\mu^{p,e}\le\int f\,d\gamma$; Theorem 3.3 combines finitely many test functions through Lemma 6.2.
--
--   Differences from the source:
--   - encoding: vertex set [n] → Fin n; reason: relabelling
--   - encoding: the minima defining F_g and κ_g in (5.1) → real sInf of the images of [z−2,z+2] and [−27,27]; reason: finite convex functions on R are continuous; these nonempty compact intervals give attained minima, with nonnegative values bounded below
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Lemma 6.1, (6.1)–(6.2), p.11 (PDF p.11); Section 6 preamble on p.11

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
import Definitions.Def_OnlineCarpoolingLei_Oblivious_ConvexOrder
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Majorant

open MeasureTheory

namespace OnlineCarpoolingLei.Oblivious

/-- Lemma 6.1 (p.11). Fix an edge `e = 1_u − 1_v` and `f ∈ C₊`. Then `Ψ_f ∈ C₊`,
(6.1) `∫ Ψ_f dγ ≤ ∫ f dγ`, and (6.2) for every `x` there is `q ∈ B_x` with
`q f(x + e) + (1 − q) f(x − e) ≤ Ψ_f(x)`. -/
theorem convex_majorant {n : ℕ} (e : Edge n) (f : (Fin n → ℝ) → ℝ) (hf : IsCPlus f) :
    IsCPlus (psiF e f) ∧
    ∫ x, psiF e f x ∂gamma n ≤ ∫ x, f x ∂gamma n ∧
    ∀ x : Fin n → ℝ, ∃ q ∈ forced e x,
      q * f (x + e.vecR) + (1 - q) * f (x - e.vecR) ≤ psiF e f x := by sorry

end OnlineCarpoolingLei.Oblivious
