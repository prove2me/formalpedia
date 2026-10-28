-- Prove2me | Theorems.Thm_MatrixAnalytic_Stability_general_drift_criterion
-- name    : MatrixAnalytic.Stability.general_drift_criterion
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:53.534852+00:00
-- url     : https://prove2.me/theorems/1f0687ac-7b6d-4e31-8701-8e64f687ef27
-- title:
--   Theorem 7.3.1 — drift criterion for a reducible phase matrix A in the block form (7.11)
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, and assume $P$ is stochastic and irreducible. Assume the stochastic matrix $A = A_0 + A_1 + A_2$ is partitioned as in (7.11), with $K \ge 1$ diagonal blocks $C^{(1)}, \dots, C^{(K)}$ that are irreducible, and with $D^{(0)}$ substochastic: its row sums are at most one, and at least one is strictly less than one (when $\phi(0)$ is nonempty). For each $k$ let $\gamma^{(k)}$ be the stationary probability vector of $C^{(k)}$, and let $C_r^{(k)}$ be the corresponding diagonal block of $A_r$ (7.12). Then:
--
--   1. the QBD is recurrent if and only if $\gamma^{(k)}C_2^{(k)}\mathbf 1 \ge \gamma^{(k)}C_0^{(k)}\mathbf 1$ for all $k$;
--   2. it is positive recurrent if and only if all these inequalities are strict;
--   3. it is transient if and only if $\gamma^{(k)}C_2^{(k)}\mathbf 1 < \gamma^{(k)}C_0^{(k)}\mathbf 1$ for at least one $k$.
--
--   This extends Theorem 7.2.3, the case $K = 1$ and $\phi(0) = \emptyset$, to reducible phase matrices.
--
--   **Formalization Note** The partition is a labelling of the phases by `Option (Fin K)` (`none` is $\phi(0)$); see the definition item for (7.11). "Substochastic" is the definition of p. 148; row sums of $D^{(0)}$ are at most one automatically, so the hypothesis states only that, if $\phi(0)$ is nonempty, some row of $D^{(0)}$ sums to less than one. Read this way the statement fails when $\phi(0)$ contains a closed class of $A$ (finding F3 of this mission); the corrected variant replaces the hypothesis by the convergence of $\sum_\nu (D^{(0)})^\nu\mathbf 1$, which the proof uses.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 160, Theorem 7.3.1; p. 159, Eqs. (7.11)–(7.12)

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Reducible

open scoped ENNReal

namespace MatrixAnalytic.Stability

/-- Theorem 7.3.1 (p. 160), as printed. The QBD is irreducible with finitely many phases, and
`A = A₀ + A₁ + A₂` has the block form (7.11): `K ≥ 1` irreducible diagonal blocks `C^{(k)}` on the
classes of `φ`, and a block `D^{(0)}` on `φ(0)` that is substochastic in the sense of p. 148
(row sums at most one, at least one of them strictly less than one; `φ(0)` may be empty).
With `γ^{(k)}` the stationary probability vector of `C^{(k)}`: the QBD is recurrent iff
`γ^{(k)}C₂^{(k)}1 ≥ γ^{(k)}C₀^{(k)}1` for all `k`, positive recurrent iff all these inequalities
are strict, and transient iff `γ^{(k)}C₂^{(k)}1 < γ^{(k)}C₀^{(k)}1` for some `k`. -/
theorem general_drift_criterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (K : ℕ) (hK : 1 ≤ K) (φ : ι → Option (Fin K))
    (hform : IsBlockForm711 (matA A₀ A₁ A₂) φ)
    (hD : (∃ i : ι, φ i = none) →
      ∃ i : ι, φ i = none ∧
        ∑ j ∈ Finset.univ.filter (fun j => φ j = none), matA A₀ A₁ A₂ i j < 1)
    (γ : Fin K → ι → ℝ) (hγ : ∀ k : Fin K, IsClassStationary (matA A₀ A₁ A₂) φ k (γ k)) :
    (IsRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      ∀ k : Fin K, classRate A₀ φ k (γ k) ≤ classRate A₂ φ k (γ k)) ∧
    (IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      ∀ k : Fin K, classRate A₀ φ k (γ k) < classRate A₂ φ k (γ k)) ∧
    (IsTransientChain (qbdP B A₀ A₁ A₂) ↔
      ∃ k : Fin K, classRate A₂ φ k (γ k) < classRate A₀ φ k (γ k)) := by sorry

end MatrixAnalytic.Stability
