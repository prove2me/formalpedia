-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_qp_solution
-- name    : MDPFinance.MeanVariance.qp_solution
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:27.094578+00:00
-- url     : https://prove2.me/theorems/a1849ffd-0643-45c5-ab9e-dd86b06cf0c5
-- title:
--   Theorem 4.6.5 — explicit solution of the auxiliary problem QP(b)
-- statement:
--   With $(d_n)$ as in Eq. (4.34): a) the value functions of $QP(b)$ are
--   $$V_n(x) = \Big(\frac{xS^0_N}{S^0_n} - b\Big)^2 d_n, \qquad x\in E,$$
--   and $V_0(x_0)$ is the value of $QP(b)$; b) the optimal policy $\pi^*=(f_0^*,\dots,f_{N-1}^*)$ is
--   $$f_n^*(x) = \Big(\frac{bS^0_n}{S^0_N} - x\Big)\, C_{n+1}^{-1}\,\mathbb{E}[R_{n+1}], \qquad
--   x\in E;$$
--   c) the first and second moments of $X_N$ under $\pi^*$ are $\mathbb{E}_{x_0}^{\pi^*}[X_N] =
--   x_0S^0_Nd_0 + b(1-d_0)$ and $\mathbb{E}_{x_0}^{\pi^*}[X_N^2] = (x_0S^0_N)^2d_0 + b^2(1-d_0)$.
--
--   This is the linear-quadratic-control heart of the section: $QP(b)$'s Bellman recursion is solved
--   by the Structure Assumption (SAN) with quadratic value-function class $\{v(x)=(c_1x-c_2)^2\}$
--   and linear feedback class $\{f(x)=(c_3-x)c_4\}$, exactly analogous to the classical LQ
--   completion-of-squares argument, giving the closed form that Lemma 4.6.3 and Theorem 4.6.6 build
--   on.
--
--   **Formalization Note.** Part c)'s moments are stated for the specific policy `fstar` constructed
--   in part b), rather than reasserted as a property of "the" optimal policy, since optimal policies
--   for $QP(b)$ need not be unique in general (though the book's construction is).
--
--   **Formalization Note (moderation).** Part (b) now states that the exhibited policy is optimal
--   for $QP(b)$ (`IsOptimalQP`), which the draft had omitted.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 121-122, PDF 135-136, Theorem 4.6.5

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary
import Definitions.Def_MDPFinance_MeanVariance_QPValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.6.5 (Bäuerle–Rieder, p. 121, PDF 135). Let `(d_n)` be as in Eq. (4.34) (`d_N := 1`,
`d_n := d_{n+1}(1-ℓ_{n+1})`). For the Markov Decision Problem `QP(b)`: a) the value functions are
`V_n(x) = (xS⁰_N/S⁰_n - b)^2 d_n`, and `V_0(x_0)` is the value of `QP(b)`; b) the optimal policy
`π^* = (f_0^*,…,f_{N-1}^*)` is `f_n^*(x) = (bS⁰_n/S⁰_N - x) C_{n+1}^{-1}𝔼[R_{n+1}]` (admissible
and optimal for `QP(b)`); c) the first and second moments of `X_N` under `π^*` are
`𝔼^{π^*}_{x_0}[X_N] = x_0S⁰_Nd_0 + b(1-d_0)`, `𝔼^{π^*}_{x_0}[X_N^2] = (x_0S⁰_N)^2d_0 + b^2(1-d_0)`. -/
theorem qp_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (b : ℝ)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))) :
    (∀ n ≤ M.N, ∀ x : ℝ, M.VQP b n x = (x * M.S0 M.N / M.S0 n - b) ^ 2 * dseq n) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x : ℝ, fstar n x =
          fun k => (b * M.S0 n / M.S0 M.N - x) * ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k)) ∧
        M.IsOptimalQP b fstar ∧
        M.meanXN fstar = M.x0 * M.S0 M.N * dseq 0 + b * (1 - dseq 0) ∧
        M.meanXNsq fstar = (M.x0 * M.S0 M.N) ^ 2 * dseq 0 + b ^ 2 * (1 - dseq 0)) := by sorry

end MDPFinance.MeanVariance
