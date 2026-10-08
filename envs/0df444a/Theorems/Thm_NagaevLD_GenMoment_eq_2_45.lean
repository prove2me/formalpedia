-- Prove2me | Theorems.Thm_NagaevLD_GenMoment_eq_2_45
-- name    : NagaevLD.GenMoment.eq_2_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:26.123275+00:00
-- url     : https://prove2.me/theorems/654a2bac-4fd3-4fdd-9a9e-4cfe8008ec68
-- title:
--   (2.45), p. 767 — P(S_n ≥ x) ≤ e^{−hx} Π Ee^{hX_j}
-- statement:
--   Let $n\ge1$ and let $X_1,\dots,X_n$ be independent real random variables on a probability space, $S_n=X_1+\dots+X_n$, and $x>0$. Let $h\ge 0$ be such that $Ee^{hX_j}<\infty$ for every $j$. Then
--   $$P(S_n\ge x)\le e^{-hx}\prod_{j=1}^n Ee^{hX_j}.$$
--
--   This is the exponential Chebyshev (Chernoff) bound combined with the factorization of the moment generating function of a sum of independent summands; it is the first step of the proof of Theorem 2.5, where it is applied with $h=g'(x/n)$.
--
--   **Formalization Note** The finiteness of each $Ee^{hX_j}$ is an explicit integrability hypothesis: the page takes it for granted ("Obviously"), and without it Lean's integral of a non-integrable function is $0$, which would make the right-hand side $0$. The summands are measurable and mutually independent (`iIndepFun`), as in §0 of the paper.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 767, proof of Theorem 2.5, (2.45)

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- (2.45), p. 767: the exponential Chebyshev (Chernoff) bound for the sum of independent
summands, `P(S_n ≥ x) ≤ e^{-hx} ∏ E e^{h X_j}` for `h ≥ 0`. -/
theorem eq_2_45 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : 0 ≤ h)
    (hint : ∀ j, Integrable (fun ω => Real.exp (h * X j ω)) P) :
    P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} ≤ Real.exp (-(h * x)) * ∏ j, ∫ ω, Real.exp (h * X j ω) ∂P := by sorry

end NagaevLD.GenMoment
