-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_proposition_4_2
-- name    : GoldieRenewal.Kesten.proposition_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:17.008767+00:00
-- url     : https://prove2.me/theorems/356f66c0-176f-4b54-99d0-d70d88a7c123
-- title:
--   Proposition 4.2 [Grincevičius (1980)] — Lévy-type maximal inequality for the partial sums of a perpetuity
-- statement:
--   Let $(Q_n,M_n)$, $n=1,2,\dots$, be independent pairs of real random variables, each with the law $\mu$ of $(Q,M)$, and let $\Pi_j$, $R_n$, $\Pi_{j,n}$, $R_{j,n}$ be the partial products and sums
--
--   $$
--   \Pi_j=\prod_{k=1}^j M_k,\quad R_n=\sum_{k=1}^n\Pi_{k-1}Q_k,\quad \Pi_{j,n}=\prod_{k=j+1}^n M_k,\quad R_{j,n}=\sum_{k=j+1}^n\Pi_{j,k-1}Q_k ,
--   $$
--
--   so that $R_n=R_j+\Pi_jR_{j,n}$. Then for every $n\ge 1$ and all $x,y\in\mathbb R$,
--
--   $$
--   P\Big(\max_{j=1,\dots,n}\big(R_j+\Pi_j\,\mathrm{med}(R_{j,n}+\Pi_{j,n}y)\big)>x\Big)\le 2P\big(R_n+\Pi_ny>x\big),
--   $$
--
--   where $\mathrm{med}(X)$ is a median of the law of $X$, and the inequality holds for every choice of medians.
--
--   This extends Lévy's symmetrization inequality from sums of independent variables to the affine recursion; in the proof of Theorem 4.1 it bounds the probability that some partial sum is large by the tail of the limit.
--
--   **Formalization Note** The sequence is stored 0-based in Lean (the $i$-th Lean variable is the paper's $(Q_{i+1},M_{i+1})$). "The maximum exceeds $x$" is written as "some $j\in\{1,\dots,n\}$ has the term exceeding $x$". No condition on $(Q,M)$ beyond measurability is assumed, as in the paper, which notes that the assumption $P(M=0)=0$ of Grincevičius (1981) is not needed.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 136, Proposition 4.2 [Grincevičius (1980)]

import Mathlib
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Proposition 4.2** [Grincevičius (1980)] (Goldie, *Implicit renewal theory and tails of
solutions of random equations*, Ann. Appl. Probab. 1(1) (1991), p. 136). Let `(Q_n, M_n)`,
`n = 1, 2, …`, be independent, each with the law `μ` of `(Q, M)`. With
`Π_j = M₁ ⋯ M_j`, `R_n = Σ_{k=1}^n Π_{k−1} Q_k`, `Π_{j,n} = Π_{k=j+1}^n M_k`,
`R_{j,n} = Σ_{k=j+1}^n Π_{j,k−1} Q_k`, for all `x, y ∈ ℝ`,
`P(max_{j=1,…,n} (R_j + Π_j med(R_{j,n} + Π_{j,n} y)) > x) ≤ 2 P(R_n + Π_n y > x)`.

**Formalization Note** The sequence is stored 0-based: `Q i`, `M i` (`i = 0, 1, …`) are the
paper's `Q_{i+1}`, `M_{i+1}` (see `piProd`, `partialSum`, `piProdFrom`, `partialSumFrom`).
`med X` is any median of the law of `X`; the paper fixes none, so the inequality is asserted for
every choice `med j` of medians, `j = 1, …, n`. "max > x" is "some `j ∈ {1, …, n}` has `… > x`".
No moment or Cramér condition is assumed, as in the paper. -/
theorem proposition_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (ℝ × ℝ)) (Q M : ℕ → Ω → ℝ) (hQ : ∀ i, Measurable (Q i))
    (hM : ∀ i, Measurable (M i))
    (hindep : iIndepFun (fun i ω => (Q i ω, M i ω)) P)
    (hlaw : ∀ i, P.map (fun ω => (Q i ω, M i ω)) = μ)
    (n : ℕ) (x y : ℝ) (med : ℕ → ℝ)
    (hmed : ∀ j ∈ Finset.Icc 1 n,
      IsMedian (P.map (fun ω => partialSumFrom Q M j n ω + piProdFrom M j n ω * y)) (med j)) :
    P {ω | ∃ j ∈ Finset.Icc 1 n, x < partialSum Q M j ω + piProd M j ω * med j}
      ≤ 2 * P {ω | x < partialSum Q M n ω + piProd M n ω * y} := by sorry

end GoldieRenewal.Kesten
