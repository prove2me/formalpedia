-- Prove2me | Theorems.Thm_OnlineGND_eq_22_24
-- name    : OnlineGND.eq_22_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:06.373919+00:00
-- url     : https://prove2.me/theorems/aa67554d-4c41-4833-954a-c3aaee371c1e
-- title:
--   (22)–(24) — the modified objective satisfies $\overline A\le e\tau\rho\sum_i y_i$
-- statement:
--   Consider GND with weighted power costs $c_ex^{\alpha_e}$ ($c_e\ge0$, $\alpha_e\ge1$), weights $w_{i,e}\ge1$, $\alpha=\max_e\alpha_e$, $E_1=\{e:\alpha_e=1\}$, and a $\tau$-approximate min-cost oracle ($\tau\ge1$). Run the online algorithm (20) with a parameter $\rho\ge(e\alpha)^{\alpha-1}$, and let $A$ be its final loads, $L=\sum_{e\in E_1}c_eA_e$, $H=\sum_{e\in E\setminus E_1}c_eA_e^{\alpha_e}$, and $y$ the dual solution of p.13:
--   $$y_i=\min_{p\in\mathcal P_i}\Bigl(\sum_{e\in p\cap E_1}c_ew_{i,e}+\sum_{e\in p\setminus E_1}\Bigl(\frac{c_e\alpha_e}{\rho}w_{i,e}A_e^{\alpha_e-1}+\frac{c_e\alpha_e}{e^\alpha}w_{i,e}^{\alpha_e}\Bigr)\Bigr).$$
--   Then the modified objective $\overline A=e\rho L+H$ satisfies
--   $$e\rho\,L+H\ \le\ e\tau\rho\sum_{i=1}^Ny_i.$$
--
--   This is the per-request accounting of the proof of Theorem 6, summed over all requests.
--
--   Differences from the source:
--   - generalization: the proof's parameter $\rho=(e\tau\alpha)^{\alpha-1}$ (with the condition $\rho\ge(e\alpha)^{\alpha-1}$ it ensures for (17)) → any $\rho\ge(e\alpha)^{\alpha-1}$; reason: (22)–(24) use only this condition, and $(e\tau\alpha)^{\alpha-1}$ satisfies it
--   - encoding: $\alpha=\max_e\alpha_e$ → $\max(1,\max_e\alpha_e)$; reason: equal for $E\ne\emptyset$ since $\alpha_e\ge1$
--   - encoding: a $\tau$-approximation algorithm → $\tau\ge1$ and the oracle predicate on the instance's requests; reason: an approximation factor of a minimization problem is at least $1$
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §4.1, proof of Theorem 6, (22)–(24), p.13

import Definitions.Def_OnlineGND_DualFitting

namespace OnlineGND

/-- **(22)–(24)** (Nagarajan & Wang, arXiv:2007.07721v1, §4.1, proof of Theorem 6, p.13):
"So we obtain `Ā ≤ eτρ Σ_{i=1}^N yᵢ`." For the online algorithm (20) with parameter
`ρ ≥ (eα)^{α−1}` and a `τ`-approximate oracle, with final loads `A`, `L = Σ_{e∈E₁} cₑAₑ`,
`H = Σ_{e∈E∖E₁} cₑAₑ^{αₑ}` and the dual `yᵢ` of p.13,
`e ρ L + H ≤ e τ ρ Σᵢ yᵢ`.

**Formalization Note.** `α = alphaMax α`. The condition `ρ ≥ (eα)^{α−1}` is the one (17) uses (p.11);
it implies the paper's standing `ρ ≥ 1`. -/
theorem eq_22_24 {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (τ : ℝ) (hτ : 1 ≤ τ) (O : Request E → (E → ℝ) → Finset E)
    (hO : IsApproxOracle τ reqs O) (ρ : ℝ)
    (hρ : (Real.exp 1 * alphaMax α) ^ (alphaMax α - 1) ≤ ρ) :
    Real.exp 1 * ρ * costL c α (load reqs (powerAlg c α ρ O reqs))
        + costH c α (load reqs (powerAlg c α ρ O reqs)) ≤
      Real.exp 1 * τ * ρ * ∑ i, dualY c α ρ (load reqs (powerAlg c α ρ O reqs)) (reqs i) := by sorry

end OnlineGND
