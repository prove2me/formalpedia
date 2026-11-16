-- Prove2me | Theorems.Thm_FourierRankQLB_Supplement_theorem_7_10
-- name    : FourierRankQLB.Supplement.theorem_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:23:32.559515+00:00
-- url     : https://prove2.me/theorems/3988055f-66e7-4245-b64d-7f5de4b40077
-- title:
--   Theorem 7.10 — approximately feasible optimization over $\{K_{n^2,Q}\}$ at tolerance $\delta_n = \Theta(n^{-2})$ needs $\Omega(n/(\log n\log\log n))$ membership queries
-- statement:
--   With the notation of Theorem 7.7, let $\gamma = \min\{1,\rho^2/49,\Delta_+,\Delta_-/3\}$ (Eqs. (89)–(90)), $\delta_{0,n} = \gamma\,\bar g_n^2$ (Eq. (91)), and
--
--   $$
--   \delta_n := n^2\,\delta_{0,n}, \qquad \mathcal K_n^{\mathrm{app}} := \{K_{n^2,Q} : Q\in O(d_n)\} \quad (92),
--   $$
--
--   with radii $r_n^{\mathrm{app}} = r_s$ and $R_n^{\mathrm{app}} = R_s$ at the scale $s = n^2$.
--
--   **Theorem.** For every sufficiently large $n$:
--
--   1. $\delta_n = \Theta(n^{-2})$;
--   2. every $K\in\mathcal K_n^{\mathrm{app}}$ satisfies $B_2(0,r_n^{\mathrm{app}})\subseteq K\subseteq B_2(0,R_n^{\mathrm{app}})$, with $r_n^{\mathrm{app}} = \Theta(n^2)$ and $R_n^{\mathrm{app}} = \Theta(n^3)$;
--   3. $R_n^{\mathrm{app}} - r_n^{\mathrm{app}} \ge \tfrac12 R_n^{\mathrm{app}}$ and $r_n^{\mathrm{app}}\delta_n/R_n^{\mathrm{app}} = O(n^{-3})$;
--   4. on every nonempty finite grid fixed in advance, every approximately feasible optimizer with tolerance $\delta_n$ that works (with probability at least $2/3$) for every $K\in\mathcal K_n^{\mathrm{app}}$ and every unit objective requires
--
--   $$
--   \Omega\Big(\frac{n}{\log n\,\log\log n}\Big)
--   $$
--
--   exact membership queries in the worst case.
--
--   Precisely: there are $n_0$ and positive constants, independent of $n$, of the grid, of the workspace and of the optimizer, such that the two-sided bounds of items 1–2, the bound of item 3 and the lower bound $c\,n/(\log n\log\log n) \le T$ of item 4 hold for all $n\ge n_0$.
--
--   This is the inverse-iteration bound for approximately feasible optimization; Theorem 5.1 removes the factor $\log n\log\log n$ for the same family and tolerance.
--
--   **Formalization Note** Success means the published event (8): $\operatorname{dist}(\hat y, K)\le\delta_n$ and $c^\top\hat y \ge h_{K^{-\delta_n}}(c) - \delta_n$. The family, $\delta_n$ and the radii are the explicit ones of the statement and its proof; only $n_0$ and the asymptotic constants are existential. $\log$ is the natural logarithm.
--
--   Differences from the source:
--
--   - generalization: one optimizer (one algorithm, invoked with each unit objective c) using exact membership on the grid G → an algorithm alg c for each objective c, each on L²(G) ⊗ ℂ² ⊗ W_c with its own workspace W_c and a POVM on ℝⁿ, with (alg c).T ≤ T for all c; reason: covers more optimizers (the published goal's convention); a single algorithm with one workspace is the case of constant W_c
--   - encoding: requires T ≥ … queries in the worst case → every uniform bound T on the per-invocation query counts satisfies T ≥ …; reason: equivalent to a bound on the worst-case query count
--   - encoding: the grid G ⊆ ℝⁿ and exact membership on G → G : Finset (Ambient n), nonempty, with the published hardOracle on QReg (counting measure on G) and labels Subtype.val; reason: the base mission's published membership model (Theorem 4.4); same oracles
--   - reading: for every sufficiently large n; δ_n = Θ(n^{-2}), r^app = Θ(n²), R^app = Θ(n³), r^app δ_n / R^app = O(n^{-3}), Ω(n/(log n log log n)) → ∃ n_0 and positive constants c_1, C_1, c_2, C_2, c_3, C_3, C_4, c_5, all before ∀ n ≥ n_0, with the corresponding two-sided, upper and lower bounds; reason: standard reading of the asymptotic notation with constants uniform in n, the grid, the workspace and the optimizer
--   - encoding: r_n^app, R_n^app (the radii of K_{n²,Q}) → rs n (n²), Rs n (n²) (Eq. (39) at s = n²); reason: the values the proof (p.45) uses
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 7.10, p.44 (δ_{0,n} Eqs. (89)–(91), p.43; radii p.45; r_s, R_s Eq. (39), p.25)

import Mathlib
import Definitions.Def_FourierRankQLB_hardOracle
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
import Definitions.Def_FourierRankQLB_approxSuccess
import Definitions.Def_FourierRankQLB_rs
import Definitions.Def_FourierRankQLB_Rs__d75a51
import Definitions.Def_FourierRankQLB_Supplement_deltaN

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- Theorem 7.10 (Approximately feasible optimization lower bound). For every sufficiently large `n`,
set `δ_n := n² δ_{0,n} = Θ(n⁻²)` and consider the family `K_n^app := {K_{n²,Q} : Q ∈ Q_n}` (92). For
every `K ∈ K_n^app`, `B₂(0, r_n^app) ⊆ K ⊆ B₂(0, R_n^app)`, `r_n^app = Θ(n²)`, `R_n^app = Θ(n³)`.
Moreover, `R_n^app - r_n^app ≥ R_n^app/2` and `r_n^app δ_n / R_n^app = O(n⁻³)`. Every approximately
feasible optimizer with tolerance `δ_n` that works for every `K ∈ K_n^app` and every unit objective
requires `Ω(n/(log n log log n))` exact membership queries in the worst case, on every nonempty finite
grid fixed in advance.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 7.10, p. 44 (`δ_{0,n}`: Eqs. (89)–(91), p. 43; `r_s, R_s`: Eq. (39), p. 25; radii of
the proof, p. 45).

**Formalization Note.** "For every sufficiently large `n`" is `∃ n₀, ∀ n ≥ n₀`, and each `Θ`, `O`,
`Ω` is a pair of (or one) positive constants; all of them are chosen before `n` and are uniform over
`n`, grids, workspaces and optimizers. The family, `δ_n`, `r_n^app = r_{n²}` and `R_n^app = R_{n²}` are
the explicit ones of the statement and its proof. The optimizer model is that of Theorem 7.7, with the
approximately feasible success event (8) of tolerance `δ_n`. `log` is the natural logarithm. -/
theorem theorem_7_10 :
    ∃ (n₀ : ℕ) (c₁ C₁ c₂ C₂ c₃ C₃ C₄ c₅ : ℝ), 0 < c₁ ∧ 0 < C₁ ∧ 0 < c₂ ∧ 0 < C₂ ∧ 0 < c₃ ∧
      0 < C₃ ∧ 0 < C₄ ∧ 0 < c₅ ∧ ∀ n : ℕ, n₀ ≤ n →
      (c₁ / (n : ℝ) ^ 2 ≤ deltaN n ∧ deltaN n ≤ C₁ / (n : ℝ) ^ 2) ∧
      (∀ Q : Od (dn n), Metric.closedBall (0 : Ambient n) (rs n ((n : ℝ) ^ 2)) ⊆
          hardBody ((n : ℝ) ^ 2) Q ∧
        hardBody ((n : ℝ) ^ 2) Q ⊆ Metric.closedBall (0 : Ambient n) (Rs n ((n : ℝ) ^ 2))) ∧
      (c₂ * (n : ℝ) ^ 2 ≤ rs n ((n : ℝ) ^ 2) ∧ rs n ((n : ℝ) ^ 2) ≤ C₂ * (n : ℝ) ^ 2) ∧
      (c₃ * (n : ℝ) ^ 3 ≤ Rs n ((n : ℝ) ^ 2) ∧ Rs n ((n : ℝ) ^ 2) ≤ C₃ * (n : ℝ) ^ 3) ∧
      Rs n ((n : ℝ) ^ 2) / 2 ≤ Rs n ((n : ℝ) ^ 2) - rs n ((n : ℝ) ^ 2) ∧
      rs n ((n : ℝ) ^ 2) * deltaN n / Rs n ((n : ℝ) ^ 2) ≤ C₄ / (n : ℝ) ^ 3 ∧
      ∀ G : Finset (Ambient n), G.Nonempty →
        ∀ {W : Ambient n → Type} [∀ c, NormedAddCommGroup (W c)] [∀ c, InnerProductSpace ℂ (W c)]
          [∀ c, CompleteSpace (W c)]
          (alg : ∀ c, QueryAlg (QReg (Measure.count : Measure G) (W c)) (Ambient n)) (T : ℕ),
          (∀ c, (alg c).T ≤ T) →
          (∀ (Q : Od (dn n)) (c : Ambient n), ‖c‖ = 1 →
            2 / 3 ≤ (alg c).outcomeProb (fun _ => hardOracle (Measure.count : Measure G) (W c)
                Subtype.val measurable_subtype_coe ((n : ℝ) ^ 2) Q)
              (approxSuccess (hardBody ((n : ℝ) ^ 2) Q) c (deltaN n))) →
          c₅ * (n : ℝ) / (Real.log n * Real.log (Real.log n)) ≤ T := by sorry

end Supplement

end FourierRankQLB
