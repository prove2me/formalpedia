-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_lemma_11
-- name    : LogBarrierIPM.Iterations.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:07:28.021094+00:00
-- url     : https://prove2.me/theorems/64bef6fd-a545-4113-84dc-48f89d17da50
-- title:
--   Lemma 11 — $\log_t|\det\mathbf M(t)|$ and $\operatorname{val}(\det\mathbf M)$ differ by at most $\log_t d!$ (for $t>1$)
-- statement:
--   Let $\mathbf M$ be a $d\times d$ monomial matrix, with entries $\epsilon_{ij}t^{\alpha_{ij}}$, $\epsilon_{ij}\in\{\pm1\}$, $\alpha_{ij}\in\mathbb R\cup\{-\infty\}$. Then for every $t>1$,
--   $$\log_t|\det\mathbf M(t)|\le\operatorname{val}(\det\mathbf M)+\log_t d!,$$
--   and if moreover $t\ge(d!)^{1/\eta(\mathbf M)}$, then
--   $$\operatorname{val}(\det\mathbf M)\le\log_t|\det\mathbf M(t)|+\log_t d!.$$
--   Here $\log_t0=-\infty$, $\operatorname{val}(\det\mathbf M)$ is the largest exponent with a non-zero collected coefficient in the permutation expansion of $\det\mathbf M$, and $\eta(\mathbf M)$ is the smallest positive gap between two permutation exponents (if $\eta(\mathbf M)=+\infty$ the threshold is $t\ge1$).
--
--   The lemma bounds the numerical value of a determinant with monomial entries by its leading exponent, with an error independent of the exponents. By Cramer's rule it controls the vertices of polyhedra with monomial data, which gives the explicit threshold on $t$ in the main theorem.
--
--   **Formalization Note** The page states the first inequality for all $t>0$. That is false for $0<t<1$: for $\mathbf M=\begin{pmatrix}t&1\\1&1\end{pmatrix}$ one has $\det\mathbf M(t)=t-1$ and $\operatorname{val}(\det\mathbf M)=1$, so at $t=1/2$ the left side is $\log_{1/2}(1/2)=1$ while the right side is $1+\log_{1/2}2=0$. The proof uses $t^{\beta_k-\beta_1}\le1$, which needs $t\ge1$, and $\log_t$ needs $t\ne1$; both inequalities are therefore stated for $t>1$. The threshold condition $t\ge(d!)^{1/\eta}$ is imposed only when $\eta(\mathbf M)$ is a real number. The Puiseux field is replaced by the combinatorial description of the definitions module.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 13, Lemma 11 (repaired: t > 1)

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_LogMetrics
import Definitions.Def_LogBarrierIPM_Iterations_MonomialMatrix

namespace LogBarrierIPM.Iterations

/-- Lemma 11 (p. 13), for `t > 1`. Let `𝐌` be the `d × d` monomial matrix with entries
`ε_{ij} t^{α_{ij}}` (`ε_{ij} ∈ {±1}`, `α_{ij} ∈ ℝ ∪ {−∞}`). Then
`log_t |det 𝐌(t)| ≤ val(det 𝐌) + log_t d!`, and, if moreover `t ≥ (d!)^{1/η(𝐌)}`,
`val(det 𝐌) ≤ log_t |det 𝐌(t)| + log_t d!` (with `log_t 0 = −∞`; the threshold condition is
`t ≥ 1` when `η(𝐌) = +∞`). -/
theorem lemma_11 {d : ℕ} (α : Matrix (Fin d) (Fin d) (WithBot ℝ))
    (ε : Matrix (Fin d) (Fin d) ℝ) (hε : ∀ i j, ε i j = 1 ∨ ε i j = -1) (t : ℝ) (ht : 1 < t) :
    logt t |(monoEval α ε t).det| ≤
        valDet α ε + ((Real.logb t (Nat.factorial d) : ℝ) : WithBot ℝ) ∧
      ((∀ η : ℝ, etaM α = (η : WithTop ℝ) → (Nat.factorial d : ℝ) ^ (1 / η) ≤ t) →
        valDet α ε ≤
          logt t |(monoEval α ε t).det| + ((Real.logb t (Nat.factorial d) : ℝ) : WithBot ℝ)) := by sorry

end LogBarrierIPM.Iterations
