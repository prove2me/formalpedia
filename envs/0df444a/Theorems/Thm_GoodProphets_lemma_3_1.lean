-- Prove2me | Theorems.Thm_GoodProphets_lemma_3_1
-- name    : GoodProphets.lemma_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:24:20.220242+00:00
-- url     : https://prove2.me/theorems/c6e128cc-0d3a-4cde-a263-31126f2d699d
-- title:
--   Lemma 3.1 — the hindsight optimum is unchanged while the actions taken stay below an optimal solution
-- statement:
--   Fix $\vec N$ and lower bounds $\vec y\le\vec y'$. Let $\vec x^\star$ be an optimal solution of $\min_{\vec x\ge\vec y}f_{\vec N}(\vec x)$ with $\vec y'\le\vec x^\star$. Then
--   $$
--   \min_{\vec x\ge\vec y'}f_{\vec N}(\vec x)=\min_{\vec x\ge\vec y}f_{\vec N}(\vec x).
--   $$
--   In the paper's notation, with $\vec y=\vec x^{\mathrm{ALG}}(t_a-1)$ and $\vec y'=\vec x^{\mathrm{ALG}}(t_b-1)$ for periods $t_a<t_b$: if $x^{\mathrm{ALG}}_{\theta j}(t_b-1)\le\mathrm{OPT}^{t_a}_{\theta j}$ for every action, then $\mathrm{OPT}^{t_a}=\mathrm{OPT}^{t_b}$. Actions that stay within an optimal hindsight plan incur no loss. This is the accounting principle behind the whole analysis.
--
--   Differences from the source:
--   - generalization: the lower bounds x^ALG(t_a − 1) ≤ x^ALG(t_b − 1) of two periods t_a < t_b of an algorithm → arbitrary arrays y ≤ y′; reason: x^ALG is non-decreasing in t, so the paper's case is the instance y = x^ALG(t_a − 1), y′ = x^ALG(t_b − 1)
--   - reading: OPT^{t_a}_θj, the optimal solution of OPT^{t_a} → any optimal solution x⋆ of min_{x ≥ y} f_N; reason: the lemma uses only optimality and feasibility of the solution; it covers the selected solution of Assumption 2
--   - generalization: the standing assumptions of §2 (N the arrival counts, f_N real-valued) → any N, any instance; reason: the proof uses only feasibility and optimality; it specializes to the paper's setting
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Lemma 3.1, p.10 (proof p.25, A.2)

import Mathlib
import Definitions.Def_GoodProphets_lpObj

namespace GoodProphets

/-- **Lemma 3.1** (Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.10): "Consider any two periods
`t_a < t_b`; if, for every action `a_θj`, we have `x^ALG_θj(t_b − 1) ≤ OPT^{t_a}_θj`, then the
objective values `OPT^{t_a} = OPT^{t_b}`."

Stated for arbitrary lower bounds `y ≤ y′` in place of `x^ALG(t_a − 1) ≤ x^ALG(t_b − 1)`: if `x⋆`
is an optimal solution of `min_{x ≥ y} f_N(x)` and `y′ ≤ x⋆`, then
`min_{x ≥ y′} f_N(x) = min_{x ≥ y} f_N(x)`.

**Formalization Note** `OPT^t` is the problem `min_x f_N(x)` s.t. `x ≥ x^ALG(t − 1)` (p.10) and
`optVal I N y` its value. "`OPT^{t_a}_θj`" is any optimal solution of `OPT^{t_a}`. -/
theorem lemma_3_1 {k ℓ r m : ℕ} (I : Instance k ℓ r m) (N : Fin k → ℝ)
    (y y' xstar : Fin k → Fin ℓ → ℝ) (hyy' : ∀ θ j, y θ j ≤ y' θ j)
    (hopt : IsOptIn I N y xstar) (hle : ∀ θ j, y' θ j ≤ xstar θ j) :
    optVal I N y' = optVal I N y := by sorry

end GoodProphets
