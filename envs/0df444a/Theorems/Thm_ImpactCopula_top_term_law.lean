-- Prove2me | Theorems.Thm_ImpactCopula_top_term_law
-- name    : ImpactCopula.top_term_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:56:54.039678+00:00
-- url     : https://prove2.me/theorems/b189b34b-3044-4883-a7e9-e62e06a83f63
-- title:
--   Proof of Theorem 2, "only if" — $P(\hat g(U_{N:N},V_N) \le y) = \int_0^1 D_1\hat C(u,F_\theta(y))\,N u^{N-1}\,du$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ with marginal distribution function $F_\theta$ of the second coordinate, let $\hat C$ be a copula, and let $\hat g(u,w) = F_\theta^{-1}(\hat g_u(w))$ be the mixture function (15) built from $\hat C$. Let $N \ge 1$ and let $U_1,\dots,U_N,V_1,\dots,V_N$ be independent uniform on $(0,1)$, with $U_{N:N} = \max_i U_i$. Then for every $y \in \mathbb R$,
--
--   $$
--   P\big(\hat g(U_{N:N}, V_N) \le y\big) = \int_0^1 D_1\hat C\big(u, F_\theta(y)\big)\, N u^{N-1}\, du .
--   $$
--
--   The paper uses this for a linearly interpolating copula $\hat C$ of $F$ and, "similarly", for the copula $C$ of Theorem 2; comparing the two for every $N$ gives (A.82).
--
--   Differences from the source:
--   - generalization: $\hat C$ a (linearly interpolating) copula of $F$, resp. $C$ a copula of $F$ → any copula $\hat C$; reason: the computation uses only Lemma 4 and Remark 1, which hold for every copula; a copula of $F$ is a copula, so the statement specializes to both of the paper's uses.
--   - encoding: $U_{N:N}$, $V_N$, $P$ → published `orderStat` at the 0-based index $N-1$, coordinate $N-1$ of $V$, the real measure `unifPair N`; reason: Lean convention; same statement.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, "only if", display following (A.81), p.82 (PDF p.85)

import Mathlib
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_ImpactCopula_cdfTheta
import Definitions.Def_ImpactCopula_mpdd
import Definitions.Def_ImpactCopula_mixture
import Definitions.Def_ImpactCopula_unifPair
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat

open MeasureTheory

namespace ImpactCopula

/-- **The law of the top term** `ĝ(U_{N:N}, V_N)`, proof of Theorem 2, "only if", Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.82
(PDF p.85): for any `y ∈ ℝ`,
`P(ĝ(U_{N:N}, V_N) ≤ y) = ∫₀¹ D₁Ĉ(u, F_θ(y)) N u^{N−1} du`
(and "similarly" for `C`).

**Formalization Note.** `ĝ` is the mixture function (15) built from the copula `Ĉ` (`mixture`).
`(U, V)` has law `unifPair N`; `U_{N:N}` is the published `orderStat` at the 0-based index
`⟨N - 1, _⟩`, and `V_N` is the coordinate `N - 1` of `V`. The display is used for a linearly
interpolating copula of `F` and for the copula `C` of `F`; it holds for every copula, which is how
it is stated. -/
theorem top_term_law (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (Chat : ℝ → ℝ → ℝ)
    (hChat : ActuarialValuation.coIsCopula Chat) (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    (unifPair N).real
        {p : (Fin N → ℝ) × (Fin N → ℝ) |
          mixture Chat μ (ImpactInvesting.Portfolio.orderStat p.1 ⟨N - 1, by omega⟩)
            (p.2 ⟨N - 1, by omega⟩) ≤ y} =
      ∫ u in (0 : ℝ)..1, mpdd Chat u (cdfTheta μ y) * ((N : ℝ) * u ^ (N - 1)) := by sorry

end ImpactCopula
