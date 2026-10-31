-- Prove2me | Theorems.Thm_MultiUnitProphet_theorem_1
-- name    : MultiUnitProphet.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:35.67161+00:00
-- url     : https://prove2.me/theorems/94eb90ee-c02c-44a2-8175-a7f042f2aabd
-- title:
--   Theorem 1 — the balancing static price earns at least $\phi_k=\delta_k(X^{\lambda_k})=\mu_k(X^{\lambda_k})$ of the expected optimal welfare
-- statement:
--   Let $X^\lambda$ be a Poisson random variable with rate $\lambda$, and let $\lambda_k$ be the rate with $\delta_k(X^{\lambda_k})=\mu_k(X^{\lambda_k})$, where $\delta_k(X)=\mathbb P[X\le k-1]$ and $\mu_k(X)=\frac1k\mathbb E[\min\{X,k\}]$. For every supply $k\ge1$:
--
--   1. the rate $\lambda_k\ge0$ exists and is unique;
--   2. every atomless instance with $n>k$ buyers has a price $\pi$ with $\delta_k(X_\pi)=\mu_k(X_\pi)$, so the pricing scheme $\boldsymbol\pi$ is well defined;
--   3. for every instance $\mathcal F$ (any $n$, any arrival order) and every price $p$ with $\delta_k(X_p)=\mu_k(X_p)$,
--   $$\frac{\mathrm{Welfare}(p,k,\mathcal F)}{\mathrm{Opt}(k,\mathcal F)}\ \ge\ \phi_k:=\delta_k(X^{\lambda_k})=\mu_k(X^{\lambda_k}).$$
--
--   Thus the competitive ratio of the static pricing scheme that equalizes the probability of not selling out with the expected fraction of units sold is at least $\phi_k$ ($\phi_1=1/2$, $\phi_2\approx0.585$, $\phi_3\approx0.630$), and $\phi_k\to1$ as $k\to\infty$.
--
--   **Formalization Note** The ratio bound is the product inequality $\phi_k\cdot\mathrm{Opt}\le\mathrm{Welfare}$ in $[0,\infty]$ for every instance.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - encoding: n distributions on the nonnegative reals, buyer t drawn independently from F_t, F_t the t-th arriving distribution → F : Fin n → Measure ℝ with IsInstance F (probability measures with F t (−∞,0) = 0), values drawn from Measure.pi F, index order = arrival order; reason: Lean convention for independent values; the arrival order is arbitrary because every F is quantified
--   - generalization: the scheme's price π(k, F) on atomless instances → every price p with δ_k(X_p) = µ_k(X_p), on every instance (atoms allowed) and every n; reason: π(k, F) is one such price and atomless instances with n > k are a special case
--   - encoding: a ratio Welfare/Opt or a real inequality → a product inequality in ℝ≥0∞ between lower Lebesgue integrals; reason: equivalent when 0 < Opt < ∞, covers Opt = ∞, and needs no finite-mean hypothesis
--   - reading: the buyer purchases iff her value is above the price (§2, p.6) → buys iff v_t ≥ p and fewer than k earlier buyers have v_s ≥ p; reason: matches X_p := |{t : v_t ≥ p}| (p.7), which the paper's analysis uses; for atomless laws the tie v_t = p has probability 0
--   - reading: set λ_k such that δ_k(X^{λ_k}) = µ_k(X^{λ_k}); our pricing scheme π (presupposed to exist) → clauses (1) ∃! λ_k and (2) existence of a balancing price for atomless instances with n > k; reason: the theorem's constant and scheme are well defined only through these facts (p.3 and §3, p.8); stating them keeps clause (3) from holding vacuously
--   - generalization: the WLOG assumption P[v_t > 0] > 0 (§2, p.7) → instances may contain buyers with v_t = 0 almost surely; reason: the Lean statement is true on these instances too, and instances satisfying the WLOG are a special case
--   - encoding: a Poisson random variable X^λ with rate λ → deltaPois k λ = Σ_{j<k} e^{−λ}λ^j/j! and muPois k λ = (1/k) Σ_j min{j,k} e^{−λ}λ^j/j!, with λ : ℝ≥0; reason: the Poisson law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Theorem 1, p.8 (proof: "combining Lemmas 1 and 2")

import Mathlib
import Definitions.Def_MultiUnitProphet_Model
import Definitions.Def_MultiUnitProphet_Poisson

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Theorem 1: the balancing static price earns at least `φ_k` of the expected optimal welfare.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Theorem 1, p.8: "Let Xλ be a Poisson random variable with rate λ and set λk such that
δk(Xλk) = µk(Xλk). The competitive ratio of our pricing scheme π is at least
ϕk := δk(Xλk) = µk(Xλk)."

For every supply `k ≥ 1`:
1. exactly one rate `λ_k ≥ 0` has `δ_k(X^{λ_k}) = µ_k(X^{λ_k})`;
2. every atomless instance with `n > k` buyers has a price `π` with `δ_k(X_π) = µ_k(X_π)` (the
   scheme (3.3) is well defined);
3. for every instance (any `n`, any arrival order, atoms allowed) and every price `p` with
   `δ_k(X_p) = µ_k(X_p)`: `φ_k · Opt(k, F) ≤ Welfare(p, k, F)`.

**Formalization Note.** The competitive ratio `inf_F Welfare/Opt ≥ φ_k` is written as the product
inequality in `ℝ≥0∞` for every instance. Every balancing price is covered, not one selection `π`.
A buyer buys iff `v_t ≥ p` and a unit is left. -/
theorem theorem_1 (k : ℕ) (hk : 1 ≤ k) :
    (∃! lam : ℝ≥0, deltaPois k lam = muPois k lam) ∧
    (∀ (n : ℕ) (F : Fin n → Measure ℝ), IsInstance F → (∀ t, NullSingletonClass (F t)) → k < n →
        ∃ p : ℝ, delta k F p = mu k F p) ∧
    ∀ lam : ℝ≥0, deltaPois k lam = muPois k lam →
      ∀ (n : ℕ) (F : Fin n → Measure ℝ), IsInstance F → ∀ p : ℝ, delta k F p = mu k F p →
        ENNReal.ofReal (deltaPois k lam) * opt k F ≤ welfare k F p := by sorry

end MultiUnitProphet
