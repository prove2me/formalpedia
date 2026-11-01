-- Prove2me | Theorems.Thm_MNLStability_dp_regime
-- name    : MNLStability.dp_regime
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:58.581785+00:00
-- url     : https://prove2.me/theorems/507d47a8-7117-42d1-9ecc-e9dac248d2a0
-- title:
--   §2.3 — the DP-amenable regime admits an FPTAS
-- statement:
--   There is an absolute constant $c_1>0$ such that the following holds. Take $n\ge1$ products with positive weights, non-negative prices, a finitely supported law of $M$, a capacity $C\ge1$, and an accuracy $e>0$ with $w_{\max}\le e\,w_0/n$. Let $G(U)=\sum_ir_i\,\mathbb E[\min(U_i,\mathrm{Bin}(M,w_i/w_0))]$.
--
--   1. If $e<1$, then for every inventory vector $U$: $(1-e)\,G(U)\le\mathbb E[R(U)]\le G(U)$.
--   2. Every run of the program `dpSolve` returns a vector $\hat U$ with at most $C$ units and $\mathbb E[R(\hat U)]\ge(1-e)\,\mathrm{OPT}$; when $e<1$, $\hat U$ maximizes $G$ over all vectors with at most $C$ units; and the run costs at most $c_1\,n\,C^2L_M$ unit operations.
--
--   As long as product $i$ is in stock it is purchased with probability between $(1-e)w_i/w_0$ and $w_i/w_0$, whatever else is offered, so each product's contribution depends essentially only on its own inventory. The paper cites the resulting FPTAS from Aouad et al. (2018b, App. A.3).
--
--   Differences from the source:
--   - generalization: "admits a fully polynomial-time approximation scheme via standard dynamic programming ideas" → the named program dpSolve, which returns a (1 − e)-optimal vector, with the sandwich (1 − e)G ≤ E[R] ≤ G and exact maximization of G; reason: the program witnesses the FPTAS; the sandwich is the formalized intuition of p.13
--   - reading: "fully polynomial-time" (running time polynomial in the input and 1/ε) → c₁·n·C²·L_M, with C counted in unary and L_M the bit length of the law of M; reason: the paper measures running times in nC (Theorem 1), and the law of M is part of the input (p.3)
--   - reading: running time in an unspecified model → unit-cost real RAM; reason: the paper fixes no model
--   - encoding: O(·) → an absolute constant c₁ chosen before the instance; bound on every run; reason: the usual reading of O(·)
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.3, p.13 ("The DP-amenable regime"; cited from Aouad et al. 2018b, App. A.3)

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_Gval
import Definitions.Def_MNLStability_dpSolve

namespace MNLStability

/-- **The DP-amenable regime** (SSRN:3498325, §2.3, p.13; cited from Aouad et al. 2018b, App. A.3),
for the explicit program `dpSolve`. There is an absolute constant `c₁ > 0` such that, for every
instance with `n ≥ 1` products, positive weights, non-negative prices, a finitely supported law
`pM` of `M`, a capacity `C ≥ 1`, and every accuracy `e > 0` with `w_max ≤ e·w₀/n`:
1. if `e < 1`, then for every inventory vector `U`, `(1 − e)·G(U) ≤ E[R(U)] ≤ G(U)`, where
   `G(U) = Σ_i r_i·E[min(U_i, Bin(M, w_i/w₀))]` treats every product as if offered by itself;
2. every run of `dpSolve` returns a vector `Û` with at most `C` units, with
   `E[R(Û)] ≥ (1 − e)·OPT`, that maximizes `G` among all vectors with at most `C` units when
   `e < 1`, after at most `c₁·n·C²·L_M` unit operations.

This is the fully polynomial-time approximation scheme of the regime. -/
theorem dp_regime : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (n : ℕ) (wts : Weights n), 1 ≤ n → wts.Pos → ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) →
    ∀ pM : ℕ →₀ ℝ, IsLaw pM → ∀ C : ℕ, 1 ≤ C → ∀ e : ℝ, 0 < e →
    wts.wmax ≤ e * wts.w0 / n →
      (e < 1 → ∀ U : Fin n → ℕ,
        (1 - e) * Gval wts r pM U ≤ expR wts r pM U ∧ expR wts r pM U ≤ Gval wts r pM U) ∧
      ∀ x ∈ ((dpSolve wts r pM C).run 0).support,
        norm1 x.1 ≤ C ∧ (1 - e) * opt ⟨wts, r, C, pM⟩ ≤ expR wts r pM x.1 ∧
        (e < 1 → ∀ U : Fin n → ℕ, norm1 U ≤ C → Gval wts r pM U ≤ Gval wts r pM x.1) ∧
        (x.2 : ℝ) ≤ c₁ * n * (C : ℝ) ^ 2 * LM pM := by sorry

end MNLStability
