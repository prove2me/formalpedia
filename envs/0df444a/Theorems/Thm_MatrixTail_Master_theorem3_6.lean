-- Prove2me | Theorems.Thm_MatrixTail_Master_theorem3_6
-- name    : MatrixTail.Master.theorem3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:15:08.397662+00:00
-- url     : https://prove2.me/theorems/3c765d72-9965-447f-bed6-cb0c7f203a0d
-- title:
--   Theorem 3.6 (Master Tail Bound) — P{λmax(Σ X_k) ≥ t} ≤ e^{−θt}·tr exp(Σ_k log E e^{θX_k})
-- statement:
--   Let $X_1,\dots,X_n$ be independent random $d\times d$ complex Hermitian matrices on a probability space, with $d\ge1$. For every $t\in\mathbb R$ and every $\theta>0$ at which all the matrix moment generating functions $\mathbb E e^{\theta X_k}$ exist,
--   $$\mathbb P\Bigl\{\lambda_{\max}\Bigl(\sum_k X_k\Bigr)\ge t\Bigr\} \le e^{-\theta t}\cdot\operatorname{tr}\exp\Bigl(\sum_k\log\mathbb E e^{\theta X_k}\Bigr).$$
--   Equivalently, the left side is at most $\inf_{\theta>0}\bigl\{e^{-\theta t}\operatorname{tr}\exp\bigl(\sum_k\log\mathbb E e^{\theta X_k}\bigr)\bigr\}$, which is display (3.5) of the paper.
--
--   This master inequality is the progenitor of the matrix Gaussian-series, Chernoff, Bernstein and Azuma bounds of the paper: each follows by bounding the individual matrix cumulant generating functions in the semidefinite order.
--
--   **Formalization Note.** The infimum over $\theta>0$ is stated for every $\theta>0$ at which the moment generating functions exist (every entry of $e^{\theta X_k}$ integrable); the paper admits non-existent ones, for which the right side is $+\infty$, so the reading is exact. The dimension is positive, since for $d=0$ the largest eigenvalue would be $0$ and the bound would fail for $t\le0$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 12, Theorem 3.6, display (3.5)

import Mathlib
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Master

/-- **Theorem 3.6 (Master Tail Bound for Independent Sums).** Tropp, *User-Friendly Tail Bounds for Sums of
Random Matrices*, arXiv:1004.4389v7, p. 12, display (3.5): "Consider a finite sequence `{X_k}` of independent,
random, self-adjoint matrices. For all `t ∈ ℝ`,
`P{λmax(Σ_k X_k) ≥ t} ≤ inf_{θ>0} { e^{−θt} · tr exp(Σ_k log E e^{θX_k}) }`."

Proof on the page: "Substitute the subadditivity rule for matrix cgfs, Lemma 3.4, into the Laplace transform
bound, Proposition 3.1."

**Formalization Note.**
* The finite sequence is `X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ` (complex matrices, §2.1), each `X k`
  measurable and Hermitian at every outcome, jointly independent (`iIndepFun X P`) under a probability
  measure `P`; the dimension is `d ≥ 1` (`[NeZero d]`), since for `d = 0`, `λmax = sSup ∅ = 0` and the
  bound would fail at `t ≤ 0`.
* The infimum over `θ > 0` is stated as the bound for every `θ > 0` at which all the mgfs `E e^{θX_k}` exist
  (every entry of `e^{θX_k}` integrable, `MatIntegrable`: the §2.2 regularity made explicit). The paper admits
  non-existent mgfs (p. 9), for which the right side is `+∞`; since `P ≤ inf_θ F(θ)` iff `P ≤ F(θ)` for
  every `θ`, this reading is exact. No real-valued `⨅` is used (it would be `0` on a set unbounded below).
* `E` is the entrywise expectation `mean`; `exp`/`log` are `cfc Real.exp`/`cfc Real.log`; `tr exp(·)` is
  `trExp`; `λmax` is `lambdaMax`. -/
theorem theorem3_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d n : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P) :
    ∀ (t θ : ℝ), 0 < θ → (∀ k, MatIntegrable P (fun ω => mexp (θ • X k ω))) →
      P.real {ω | t ≤ lambdaMax (∑ k, X k ω)} ≤
        Real.exp (-θ * t) * trExp (∑ k, mlog (mean P (fun ω => mexp (θ • X k ω)))) := by sorry

end MatrixTail.Master
