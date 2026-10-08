-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_supermartingale_Q
-- name    : FreedmanTail.Bernstein.supermartingale_Q
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:53:53.23722+00:00
-- url     : https://prove2.me/theorems/ec092df1-1bba-42bc-97bd-14cc614451bd
-- title:
--   Proof of (3.3) — under (3.4), {Q_λ(T_n, S_n), ℱ_n} is an expectation-decreasing martingale
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability triple with an increasing sequence of sub-$\sigma$-fields $\mathcal F_0\subset\mathcal F_1\subset\cdots$, and let $X_1,X_2,\dots$ be random variables with $X_n$ $\mathcal F_n$-measurable and square integrable. Assume condition (3.4):
--   $$X_n\le1\ \text{a.e.}\quad\text{and}\quad E\{X_n\mid\mathcal F_{n-1}\}\le0\ \text{a.e.}\qquad\text{for all }n\ge1,$$
--   with no lower bound on $X_n$. Let $S_n=X_1+\cdots+X_n$, $T_n=\sum_{i\le n}\operatorname{Var}\{X_i\mid\mathcal F_{i-1}\}$, $e(\lambda)=e^\lambda-1-\lambda$ and $Q_\lambda(v,y)=\exp\{\lambda y-e(\lambda)v\}$. Then for every $\lambda\ge0$,
--   $$\bigl\{Q_\lambda(T_n,S_n),\ \mathcal F_n:\ n=0,1,2,\dots\bigr\}$$
--   is an expectation-decreasing martingale (a supermartingale): each $Q_\lambda(T_n,S_n)$ is $\mathcal F_n$-measurable and integrable, and $E\{Q_\lambda(T_{n+1},S_{n+1})\mid\mathcal F_n\}\le Q_\lambda(T_n,S_n)$ almost surely.
--
--   This is the step on which Proposition (3.3), and through it the tail bound (4.1), rests.
--
--   **Formalization Note** "Expectation-decreasing martingale" is the paper's term for a supermartingale, rendered as Mathlib's `Supermartingale` (adapted, integrable, and the conditional expectation of a later value at most the current one). Square integrability of each $X_n$ is assumed because $V_n=\operatorname{Var}\{X_n\mid\mathcal F_{n-1}\}$ is defined through conditional expectations, which Mathlib sets to $0$ for non-integrable arguments; the page defines $V_n$ without comment.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 106 (PDF p. 7), first sentence of the proof of (3.3) Proposition

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), proof of (3.3) Proposition, p. 106: under (3.4) and `λ ≥ 0`,
`{Q_λ(T_n, S_n), ℱ_n}` is an expectation-decreasing martingale (a supermartingale). -/
theorem supermartingale_Q {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Supermartingale (fun n ω => Q lam (T ℱ X P n ω) (S X n ω)) ℱ P := by sorry

end FreedmanTail.Bernstein
