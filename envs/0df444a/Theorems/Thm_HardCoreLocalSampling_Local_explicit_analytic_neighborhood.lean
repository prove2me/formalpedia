-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_explicit_analytic_neighborhood
-- name    : HardCoreLocalSampling.Local.explicit_analytic_neighborhood
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:39.646697+00:00
-- url     : https://prove2.me/theorems/b85a558a-f027-4dca-bf90-ad0d3db4bd88
-- title:
--   Lemma 8 — Explicit common analytic neighborhood
-- statement:
--   Let $r=1/(32\Delta)$ and $M=8+2^{\Delta+2}(1+\lambda)$. Around every nonnegative real center $c\in[0,\infty)^d$, $d\le\Delta$, the function $F_d$ is analytic on the complex polydisc $|z_i-c_i|\le r$ and satisfies $|F_d(z)|\le M$ there. The root probability function $P_d$ is analytic on the same polydisc and satisfies $|P_d(z)|\le1$. Consequently
--
--   $$
--   \Bigl|\frac{\partial^\alpha F_d(c)}{\alpha!}\Bigr|\le Mr^{-|\alpha|},\qquad
--   \Bigl|\frac{\partial^\alpha P_d(c)}{\alpha!}\Bigr|\le r^{-|\alpha|}.
--   $$
--
--   These bounds control all higher Taylor coefficients uniformly in the center, including the root arity $d=\Delta$.
--
--   Differences from the source:
--   - encoding: F_d and P_d on complex arguments → explicit formulas with principal branches, with two added clauses saying they agree with the real functions at real arguments; reason: these are the formulas of the source's proof; the added clauses tie the complex and real definitions together without changing the lemma
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 8, eqs. (6)–(8), printed p.7 (PDF p.8)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 8, printed p.7 (PDF p.8), eqs. (6)–(8).
With `r = 1/(32Δ)` and `M = 8 + 2^{Δ+2}(1+λ)`, around every nonnegative real center with
`d ≤ Δ`, `F_d` and `P_d` extend analytically to the closed polydisc, with `|F_d| ≤ M`,
`|P_d| ≤ 1`, and the Taylor bounds (8). -/
theorem explicit_analytic_neighborhood (Delta : ℕ) (lam : ℚ) (hS : Standing Delta lam)
    (d : ℕ) (hd : d ≤ Delta) (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) :
    let cC : Fin d → ℂ := fun i => (c i : ℂ)
    let r : ℝ := (rParam Delta : ℝ)
    let M : ℝ := (MParam Delta lam : ℝ)
    (∀ y : Fin d → ℝ, FdC (lam : ℝ) (fun i => (y i : ℂ)) = (Fd (lam : ℝ) y : ℂ)) ∧
    (∀ y : Fin d → ℝ, PdC (lam : ℝ) (fun i => (y i : ℂ)) = (Pd (lam : ℝ) y : ℂ)) ∧
    AnalyticOnNhd ℂ (FdC (lam : ℝ)) (polydisc cC r) ∧
    (∀ z ∈ polydisc cC r, ‖FdC (lam : ℝ) z‖ ≤ M) ∧
    AnalyticOnNhd ℂ (PdC (lam : ℝ)) (polydisc cC r) ∧
    (∀ z ∈ polydisc cC r, ‖PdC (lam : ℝ) z‖ ≤ 1) ∧
    (∀ α : Fin d → ℕ, ‖taylorCoeff (FdC (lam : ℝ)) cC α‖ ≤ M * (r⁻¹) ^ mdeg α) ∧
    (∀ α : Fin d → ℕ, ‖taylorCoeff (PdC (lam : ℝ)) cC α‖ ≤ (r⁻¹) ^ mdeg α) := by sorry

end HardCoreLocalSampling.Local
