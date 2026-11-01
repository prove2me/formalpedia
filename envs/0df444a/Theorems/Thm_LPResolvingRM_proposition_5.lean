-- Prove2me | Theorems.Thm_LPResolvingRM_proposition_5
-- name    : LPResolvingRM.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:40:22.237992+00:00
-- url     : https://prove2.me/theorems/8c5caf65-3939-42e2-a761-efe5621162fa
-- title:
--   Proposition 5 — basis stability of a perturbed standard-form LP (corrected: data normalized to $|c_j|,|A_{ij}|,|b_i|\le1$)
-- statement:
--   Consider the standard-form LP $\min c^\top x$ s.t. $Ax=b$, $x\ge0$ with $m\ge1$, and assume $|c_j|\le1$, $|A_{ij}|\le1$, $|b_i|\le1$. Suppose its optimal solution $x^*$ is unique and nondegenerate: the basic set $\mathcal B^*=\{j:x^*_j>0\}$ has $m$ elements; let $\mathcal B'=\{j:x^*_j=0\}$. Let $\lambda^*$ be a dual optimal solution and define
--   $$\chi:=\min\{x^*_j:x^*_j>0\},\qquad\sigma:=\sigma_{\min}(A_{\mathcal B^*}),\qquad\delta:=\min\{c_j-A_j^\top\lambda^*:\ c_j-A_j^\top\lambda^*>0\}.$$
--   If the perturbed data $(\hat c,\hat A,\hat b)$ satisfy
--   $$\|\hat A_j-A_j\|_\infty\le\begin{cases}\frac{\min\{1,\sigma,\sigma^2\}\cdot\min\{\chi,\delta\}}{12m^2\sqrt m}&j\in\mathcal B^*\\[2pt]\frac{\sigma\delta}{12m}&j\in\mathcal B'\end{cases},\qquad|\hat c_j-c_j|\le\begin{cases}\frac{\sigma\delta}{12m}&j\in\mathcal B^*\\[2pt]\frac\delta6&j\in\mathcal B'\end{cases},\qquad|\hat b_i-b_i|\le\frac{\sigma\chi}{8\sqrt m},$$
--   then the LP $\min\hat c^\top x$ s.t. $\hat Ax=\hat b$, $x\ge0$ has a unique optimal solution, and its positive coordinates are exactly $\mathcal B^*$ (the same basic and non-basic index sets; in particular it is nondegenerate).
--
--   This is the general LP-stability result from which the stability radius of Lemma 1 is computed (Appendix E.2).
--
--   **Formalization Note** A bound $x\le K\delta$ is written as $x\le K\Psi_k$ for every $k$ with $\Psi_k>0$, so $\delta=+\infty$ when no reduced cost is positive.
--
--   Differences from the source:
--   - correction: no bound on c, A, b → |c_j| ≤ 1, |A_ij| ≤ 1, |b_i| ≤ 1; reason: the printed statement is false: c = (12, 13), A = (1, 1), b = 1 with Â = (11/12, 1) moves the optimum to x = (0, 1); c = (1/101, 1), A = (1, 100), b = 1 with ĉ₁ = 13/1212 does the same; A = [[1,0,1],[0,1,1]], b = (1000, 1), c = (0, 0, 1) with Â₂₁ = 1/68 makes (36) infeasible. Each instance satisfies (37) and violates only one of the three bounds, which the proof (pp.47–49) uses as ‖c_{B*}‖₁ ≤ m, ‖A_i‖_∞ ≤ 1, ‖b‖_∞ ≤ 1
--   - reading: δ := min{A_jᵀλ* − c_j : A_jᵀλ* − c_j > 0} → δ := min{c_j − A_jᵀλ* : c_j − A_jᵀλ* > 0}; reason: under dual feasibility Aᵀλ* ≤ c the printed set is empty; the proof uses the reduced costs Ψ_i = c_i − A_iᵀλ* > 0 (p.48, (39))
--   - reading: 'the optimal solution of (35) is also unique and nondegenerate' → (36) has a unique optimal solution whose positive coordinates are B*; reason: typo for (36): the proof, part (c), p.47, shows 'x̂ is the unique optimal solution of the perturbed LP (36)'
--   - encoding: b ∈ ℝⁿ → b ∈ ℝ^m; reason: typo: Ax = b with A ∈ ℝ^{m×n}
--   - encoding: bounds K·min{χ, δ} and K·δ → K·χ and K·Ψ_k for every k with Ψ_k > 0; reason: the same conditions; an empty minimum is +∞ rather than a junk 0
--   - encoding: unique and nondegenerate optimal solution; the bounds divide by √m → x* unique optimal, #{j : x*_j > 0} = m, and m ≥ 1; reason: nondegenerate means |B*| = m with A_{B*} square, as the proof uses
--   - encoding: λ*, the dual optimal solution → any dual optimal λ; reason: the dual optimum is unique when the primal optimum is nondegenerate
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Proposition 5, p.46 (proof pp.47–49)

import Definitions.Def_LPResolvingRM_SFOptimal

open Matrix

namespace LPResolvingRM

/-- **Proposition 5 (corrected: data normalized to `|c_j|, |A_{ij}|, |b_i| ≤ 1`)**
(arXiv:2101.11092v3, Appendix E, p.46). For the standard-form LP (35) `min cᵀx s.t. Ax = b,
x ≥ 0` with a unique and nondegenerate optimal solution `x*` (`|B*| = m` for
`B* = {j : x*_j > 0}`), let `χ := min{x*_j : x*_j > 0}`, `σ := σ_min(A_{B*})`,
`δ := min{Ψ_j : Ψ_j > 0}` with the reduced costs `Ψ_j = c_j − A_jᵀλ*` of a dual optimal `λ*`.
If

* `‖Â_j − A_j‖_∞ ≤ min{1, σ, σ²}·min{χ, δ}/(12m²√m)` for `j ∈ B*` and `≤ σδ/(12m)` for `j ∈ B'`,
* `|ĉ_j − c_j| ≤ σδ/(12m)` for `j ∈ B*` and `≤ δ/6` for `j ∈ B'`,
* `|b̂_i − b_i| ≤ σχ/(8√m)` for all `i`,

then the LP (36) `min ĉᵀx s.t. Âx = b̂, x ≥ 0` has a unique optimal solution, and it has the same
basic and non-basic index sets as `x*` (so it is nondegenerate).

**Formalization Note.** The printed statement has no bound on the data and is false (e.g.
`c = (12, 13)`, `A = (1, 1)`, `b = 1`, `Â = (11/12, 1)`); the proof (pp.47–49) uses
`‖c_{B*}‖₁ ≤ m`, `‖A_i‖_∞ ≤ 1` and `‖b‖_∞ ≤ 1`. `δ` is read with the reduced cost
`c_j − A_jᵀλ*` of (39) (the printed `A_jᵀλ* − c_j > 0` is empty under dual feasibility).
A bound `x ≤ K·δ` is written "`x ≤ K Ψ_k` for every `k` with `Ψ_k > 0`", which reads
`δ = +∞` when no reduced cost is positive. "The optimal solution of (35) is also unique" at the
end of the proposition is read as (36) (the proof, part (c), p.47). `m ≥ 1` (the bounds divide by
`√m`). -/
theorem proposition_5 {m n : ℕ} (hm : 0 < m) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hc : ∀ j, |c j| ≤ 1) (hA : ∀ i j, |A i j| ≤ 1) (hb : ∀ i, |b i| ≤ 1)
    (xstar : Fin n → ℝ) (hopt : SFOptimal c A b xstar)
    (huniq : ∀ x, SFOptimal c A b x → x = xstar)
    (hnondeg : (Finset.univ.filter fun j => 0 < xstar j).card = m)
    (lam : Fin m → ℝ) (hlam : SFDualOptimal c A b lam)
    (χ σ : ℝ) (hχ : χ = ⨅ j : {j : Fin n // 0 < xstar j}, xstar j.1)
    (hσ : σ = sigmaMin (A.submatrix id fun j : {j : Fin n // 0 < xstar j} => j.1))
    (ch : Fin n → ℝ) (Ah : Matrix (Fin m) (Fin n) ℝ) (bh : Fin m → ℝ)
    (hA_basic : ∀ j, 0 < xstar j → ∀ i,
      |Ah i j - A i j| ≤ min 1 (min σ (σ ^ 2)) * χ / (12 * m ^ 2 * Real.sqrt m) ∧
      ∀ k, 0 < reducedCost c A lam k →
        |Ah i j - A i j| ≤ min 1 (min σ (σ ^ 2)) * reducedCost c A lam k /
          (12 * m ^ 2 * Real.sqrt m))
    (hA_nonbasic : ∀ j, xstar j = 0 → ∀ i, ∀ k, 0 < reducedCost c A lam k →
      |Ah i j - A i j| ≤ σ * reducedCost c A lam k / (12 * m))
    (hc_basic : ∀ j, 0 < xstar j → ∀ k, 0 < reducedCost c A lam k →
      |ch j - c j| ≤ σ * reducedCost c A lam k / (12 * m))
    (hc_nonbasic : ∀ j, xstar j = 0 → ∀ k, 0 < reducedCost c A lam k →
      |ch j - c j| ≤ reducedCost c A lam k / 6)
    (hb_pert : ∀ i, |bh i - b i| ≤ σ * χ / (8 * Real.sqrt m)) :
    ∃ xh, SFOptimal ch Ah bh xh ∧ (∀ x, SFOptimal ch Ah bh x → x = xh) ∧
      ∀ j, (0 < xh j ↔ 0 < xstar j) := by sorry

end LPResolvingRM
