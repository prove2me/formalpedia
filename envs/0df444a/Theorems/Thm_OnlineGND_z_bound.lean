-- Prove2me | Theorems.Thm_OnlineGND_z_bound
-- name    : OnlineGND.z_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:10.79322+00:00
-- url     : https://prove2.me/theorems/858bb554-f7f3-4354-b220-22ee534f8abc
-- title:
--   §4.1, p.13 — the dual $z$-terms are at most $\rho^{-\alpha/(\alpha-1)}(\alpha-1)H$
-- statement:
--   Let $c_e\ge0$, $\alpha_e\ge1$, $\alpha=\max_e\alpha_e$, $E_1=\{e:\alpha_e=1\}$, $\beta_e=\alpha_e/(\alpha_e-1)$ for $e\notin E_1$, $\rho\ge1$, and let $A_e\ge0$ be loads. With $z_e=\frac1\rho A_e^{\alpha_e-1}$ for $e\in E\setminus E_1$ and $H=\sum_{e\in E\setminus E_1}c_eA_e^{\alpha_e}$,
--   $$\sum_{e\in E\setminus E_1}\frac{c_e\alpha_e}{\beta_e}\,z_e^{\beta_e}\ \le\ \rho^{-\frac{\alpha}{\alpha-1}}(\alpha-1)\sum_{e\in E\setminus E_1}c_eA_e^{\alpha_e}=\rho^{-\frac{\alpha}{\alpha-1}}(\alpha-1)\cdot H.$$
--
--   In the proof of Theorem 6 it bounds the penalty term of the dual objective by a multiple of the algorithm's cost $H$.
--
--   **Formalization Note** When $\alpha=1$, the set $E\setminus E_1$ is empty and both sides are $0$; Lean's $\alpha/(\alpha-1)=1/0=0$ then gives $\rho^0\cdot0\cdot H=0$, so the statement is well posed.
--
--   Differences from the source:
--   - generalization: $A$ the final loads of the algorithm → any loads $A\ge0$, any $\rho\ge1$; reason: the bound uses only $A\ge0$ and $\rho\ge1$; the algorithm's loads and parameter are instances
--   - encoding: $\alpha=\max_e\alpha_e$ → $\max(1,\max_e\alpha_e)$; reason: equal for $E\ne\emptyset$ since $\alpha_e\ge1$
--   - encoding: the exponent $\alpha/(\alpha-1)$ at $\alpha=1$ (undefined in the source) → $0$ (Lean's $1/0=0$); reason: at $\alpha=1$ the set $E\setminus E_1$ is empty and the factor $\alpha-1$ is $0$, so both sides are $0$ whatever the exponent
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §4.1, proof of Theorem 6, p.13 (the display after (24)); the same computation p.12

import Definitions.Def_OnlineGND_DualFitting

namespace OnlineGND

/-- **The z-variable bound** (Nagarajan & Wang, arXiv:2007.07721v1, §4.1, proof of Theorem 6, p.13):
with `zₑ = (1/ρ) Aₑ^{αₑ−1}` for `e ∈ E ∖ E₁`,
`Σ_{e∈E∖E₁} (cₑαₑ/βₑ) · zₑ^{βₑ} ≤ ρ^{−α/(α−1)} (α − 1) Σ_{e∈E∖E₁} cₑ Aₑ^{αₑ} = ρ^{−α/(α−1)} (α − 1) · H`.

**Formalization Note.** Stated for every nonnegative load vector `A`, not only the algorithm's final
loads. `α = alphaMax α`. When `α = 1` the set `E ∖ E₁` is empty and both sides are `0`; Lean's
`α/(α−1) = 1/0 = 0` then gives `ρ^0 (α−1) H = 0`, so the statement is not ill-posed. -/
theorem z_bound {E : Type*} [Fintype E] [DecidableEq E] (c α : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hα : ∀ e, 1 ≤ α e) (ρ : ℝ) (hρ : 1 ≤ ρ) (A : E → ℝ) (hA : ∀ e, 0 ≤ A e) :
    ∑ e ∈ Finset.univ.filter (fun e => α e ≠ 1),
        c e * α e / conjExp α e * zVar α ρ A e ^ conjExp α e ≤
      ρ ^ (-(alphaMax α / (alphaMax α - 1))) * (alphaMax α - 1) * costH c α A := by sorry

end OnlineGND
