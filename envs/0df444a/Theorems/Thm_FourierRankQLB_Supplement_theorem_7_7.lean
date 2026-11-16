-- Prove2me | Theorems.Thm_FourierRankQLB_Supplement_theorem_7_7
-- name    : FourierRankQLB.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:22:28.930991+00:00
-- url     : https://prove2.me/theorems/14cedcb7-68ab-4a70-918e-79bdd32a412d
-- title:
--   Theorem 7.7 — exactly feasible optimization over $\{K_{n,Q}\}$ at accuracy $\varepsilon_n = \Theta(n^{-2})$ needs $T \ge n/(4704\log n\log\log n)$, $n \ge 100$
-- statement:
--   For $n \ge 2$ let $d_n = 2\lfloor n/2\rfloor$, $\bar g_n = g_{d_n}$, and for $Q \in O(d_n)$ let $K_{s,Q} = \{y\in\mathbb R^n : y^\top \bar A_{n,Q}\,y \le s^2\}$ be the hard ellipsoids of Eq. (38), with radii $r_s = s/\sqrt{1+2\bar g_n}$ and $R_s = s/\sqrt{2\bar g_n}$ (Eq. (39)). Take the scale $s = n$ and the family and accuracy of Eq. (86):
--
--   $$
--   \mathcal K_n = \{K_{n,Q} : Q\in O(d_n)\}, \qquad \varepsilon_n = n\,c_\star\,\bar g_n^{3/2}, \quad c_\star = 10^{-8},
--   $$
--
--   with $r_n = r_s$ and $R_n = R_s$ at $s = n$.
--
--   **Theorem.** There are constants $c_\varepsilon, C_\varepsilon, C_3 > 0$ such that for every $n \ge 100$:
--
--   1. $c_\varepsilon n^{-2} \le \varepsilon_n \le C_\varepsilon n^{-2}$;
--   2. $r_n, R_n > 0$, and every $K \in \mathcal K_n$ satisfies $B_2(0,r_n)\subseteq K\subseteq B_2(0,R_n)$;
--   3. $R_n - r_n \ge \tfrac12 R_n$ and $r_n\varepsilon_n/R_n \le C_3 n^{-3}$;
--   4. for every nonempty finite grid $G\subseteq\mathbb R^n$ fixed in advance, every exactly feasible optimizer of accuracy $\varepsilon_n$ that, for every $K\in\mathcal K_n$ and every unit objective $c$, succeeds with probability at least $2/3$ using exact membership queries to $K$ on $G$, needs
--
--   $$
--   T \ge \frac{n}{4704\,\log n\,\log\log n} \qquad (85)
--   $$
--
--   queries in the worst case.
--
--   This is the paper's first-version reduction (inverse iteration) for exactly feasible optimization; the linear bound of the mission's goal, Theorem 5.1, removes the factor $\log n\log\log n$ for the same family.
--
--   **Formalization Note** The theorem says "there are universal constants $n_0, c_\varepsilon, C_\varepsilon, C_{lb}$ … there is an explicit family … One may take $n_0 = 100$ and $C_{lb} = 1/4704$". The Lean statement fixes $n_0 = 100$, $C_{lb} = 1/4704$ and the explicit family, accuracy and radii of the proof (Eq. (86)); the remaining constants, including that of $O(n^{-3})$, are existential and uniform in $n$. Success means the published event (7): $\hat x\in K$ and $c^\top\hat x \ge h_K(c) - \varepsilon_n$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--
--   - generalization: one optimizer (one algorithm, invoked with each unit objective c) using exact membership on the grid G → an algorithm alg c for each objective c, each on L²(G) ⊗ ℂ² ⊗ W_c with its own workspace W_c and a POVM on ℝⁿ, with (alg c).T ≤ T for all c; reason: covers more optimizers (the published goal's convention); a single algorithm with one workspace is the case of constant W_c
--   - encoding: requires T ≥ … queries in the worst case → every uniform bound T on the per-invocation query counts satisfies T ≥ …; reason: equivalent to a bound on the worst-case query count
--   - encoding: the grid G ⊆ ℝⁿ and exact membership on G → G : Finset (Ambient n), nonempty, with the published hardOracle on QReg (counting measure on G) and labels Subtype.val; reason: the base mission's published membership model (Theorem 4.4); same oracles
--   - reading: there are universal constants n_0, c_ε, C_ε, C_lb > 0 such that for every n ≥ n_0 there is an explicit family K_n … and an accuracy ε_n …; there are known parameters r_n, R_n > 0 …; one may take n_0 = 100 and C_lb = 1/4704 → n_0 = 100 and C_lb = 1/4704 fixed; K_n = {K_{n,Q} : Q ∈ O(d_n)}, ε_n = n c⋆ ḡ_n^{3/2}, r_n = r_s, R_n = R_s at s = n (Eq. (86) and its proof); ∃ c_ε, C_ε, C_3 > 0 before ∀ n ≥ 100; reason: the theorem names these values and the explicit family of its proof; fixing them gives the stronger (and intended) reading, which implies the bare existential one
--   - reading: r_n ε_n / R_n = O(n^{-3}) → ∃ C_3 > 0, ∀ n ≥ 100, r_n ε_n / R_n ≤ C_3 / n³; reason: standard reading of O(·) on the range n ≥ n_0
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 7.7, p.41 (family and accuracy Eq. (86), p.42; r_s, R_s Eq. (39), p.25; c⋆ Eq. (74), p.37)

import Mathlib
import Definitions.Def_FourierRankQLB_hardOracle
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
import Definitions.Def_FourierRankQLB_exactSuccess
import Definitions.Def_FourierRankQLB_rs
import Definitions.Def_FourierRankQLB_Rs__d75a51
import Definitions.Def_FourierRankQLB_Supplement_epsN

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- Theorem 7.7 (Exactly feasible optimization lower bound), for the explicit family of its proof.
There are universal constants `c_ε, C_ε > 0` (and the constant of `O(n⁻³)`) such that for every
`n ≥ n₀ = 100` the family `K_n = {K_{n,Q} : Q ∈ O(d_n)}` of Eq. (86) and the accuracy
`ε_n = n c⋆ ḡ_n^{3/2}` satisfy `c_ε n⁻² ≤ ε_n ≤ C_ε n⁻²`; the parameters `r_n = r_n(s = n)`,
`R_n = R_n(s = n)` are positive, every `K ∈ K_n` satisfies `B₂(0, r_n) ⊆ K ⊆ B₂(0, R_n)`,
`R_n - r_n ≥ R_n/2` and `r_n ε_n / R_n = O(n⁻³)` (84); and on any nonempty finite grid `G ⊆ ℝⁿ` fixed
in advance, every exactly feasible optimizer of accuracy `ε_n` that works for all `K ∈ K_n` and all
unit objectives, using exact membership on `G`, requires `T ≥ C_lb n/(log n log log n)` (85) queries
in the worst case, with `C_lb = 1/4704`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 7.7, p. 41 (family and accuracy: Eq. (86), p. 42; `r_s, R_s`: Eq. (39), p. 25).

**Formalization Note.** The explicit family, accuracy and radii are those the proof constructs
(Eq. (86)), and `n₀ = 100`, `C_lb = 1/4704` are the values the theorem says one may take. The
optimizer on objective `c` is the query algorithm `alg c` on the register `L²(G) ⊗ ℂ² ⊗ W_c`
(counting measure, labels the grid points), with any workspace `W_c` and a POVM on `ℝⁿ`; all of it is
chosen before `Q`. `T` bounds the number of queries of every invocation. `log` is the natural
logarithm. -/
theorem theorem_7_7 :
    ∃ cε Cε C₃ : ℝ, 0 < cε ∧ 0 < Cε ∧ 0 < C₃ ∧ ∀ n : ℕ, 100 ≤ n →
      (cε / (n : ℝ) ^ 2 ≤ epsN n ∧ epsN n ≤ Cε / (n : ℝ) ^ 2) ∧
      (0 < rs n (n : ℝ) ∧ 0 < Rs n (n : ℝ)) ∧
      (∀ Q : Od (dn n), Metric.closedBall (0 : Ambient n) (rs n (n : ℝ)) ⊆ hardBody (n : ℝ) Q ∧
        hardBody (n : ℝ) Q ⊆ Metric.closedBall (0 : Ambient n) (Rs n (n : ℝ))) ∧
      Rs n (n : ℝ) / 2 ≤ Rs n (n : ℝ) - rs n (n : ℝ) ∧
      rs n (n : ℝ) * epsN n / Rs n (n : ℝ) ≤ C₃ / (n : ℝ) ^ 3 ∧
      ∀ G : Finset (Ambient n), G.Nonempty →
        ∀ {W : Ambient n → Type} [∀ c, NormedAddCommGroup (W c)] [∀ c, InnerProductSpace ℂ (W c)]
          [∀ c, CompleteSpace (W c)]
          (alg : ∀ c, QueryAlg (QReg (Measure.count : Measure G) (W c)) (Ambient n)) (T : ℕ),
          (∀ c, (alg c).T ≤ T) →
          (∀ (Q : Od (dn n)) (c : Ambient n), ‖c‖ = 1 →
            2 / 3 ≤ (alg c).outcomeProb (fun _ => hardOracle (Measure.count : Measure G) (W c)
                Subtype.val measurable_subtype_coe (n : ℝ) Q)
              (exactSuccess (hardBody (n : ℝ) Q) c (epsN n))) →
          (n : ℝ) / (4704 * Real.log n * Real.log (Real.log n)) ≤ T := by sorry

end Supplement

end FourierRankQLB
