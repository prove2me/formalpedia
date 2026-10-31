-- Prove2me | Theorems.Thm_OnlineGND_lemma_1
-- name    : OnlineGND.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:37.671531+00:00
-- url     : https://prove2.me/theorems/a0e2f398-939d-46f0-88b7-944aa593d16e
-- title:
--   Lemma 1 — $\tfrac12 h_e \le f_e \le \max\{q_e,1\}\,h_e$ on $\{0\}\cup\mathbb R_{\ge1}$
-- statement:
--   Let $e$ be a resource with $\sigma_e\ge0$, $\xi_e>0$ and $\alpha_e\ge1$, let $f_e$ be its (D)oS cost (1), $q_e=(\sigma_e/\xi_e)^{1/\alpha_e}$, and $h_e(x)=\xi_eq_e^{\alpha_e-1}x+\xi_ex^{\alpha_e}$. For every $x\in\{0\}\cup\mathbb R_{\ge1}$,
--   $$\tfrac12\,h_e(x)\le f_e(x)\le\max\{q_e,1\}\cdot\xi_eq_e^{\alpha_e-1}\cdot x+\xi_e\cdot x^{\alpha_e}\le\max\{q_e,1\}\cdot h_e(x).$$
--
--   Thus, at loads that are $0$ or at least $1$, the (D)oS cost is within a factor $2\max\{q_e,1\}$ of a convex power function, which is the reduction of §2.
--
--   **Formalization Note** Powers are `Real.rpow`.
--
--   Differences from the source:
--   - encoding: $\xi_e\ge0$ → $\xi_e>0$; reason: $q_e=(\sigma_e/\xi_e)^{1/\alpha_e}$, used in the statement, is undefined at $\xi_e=0$
--   - encoding: $q_e^{\alpha_e-1}$ at $q_e=0$, $\alpha_e=1$ → the value $1$ (`Real.rpow`); reason: Lean convention $0^0=1$, the limit of $q_e^0$ as $q_e\to0$; it changes no instance with $q_e>0$ or $\alpha_e>1$
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, Lemma 1, p.6

import Definitions.Def_OnlineGND_DoS

namespace OnlineGND

/-- **Lemma 1** (Nagarajan & Wang, arXiv:2007.07721v1, §2, p.6). For each resource `e` and each load
`x ∈ {0} ∪ ℝ_{≥1}`,
`½ · hₑ(x) ≤ fₑ(x) ≤ max{qₑ, 1} · ξₑ qₑ^{αₑ−1} · x + ξₑ · x^{αₑ} ≤ max{qₑ, 1} · hₑ(x)`.

**Formalization Note.** `σₑ ≥ 0`, `ξₑ > 0` (so `qₑ = (σₑ/ξₑ)^{1/αₑ}` is defined) and `αₑ ≥ 1`.
Powers are `Real.rpow`; `qₑ^{αₑ−1} = 1` when `qₑ = 0`, `αₑ = 1`, as in the paper. -/
theorem lemma_1 {E : Type*} [Fintype E] (σ ξ α : E → ℝ) (e : E) (hσ : 0 ≤ σ e) (hξ : 0 < ξ e)
    (hα : 1 ≤ α e) (x : ℝ) (hx : x = 0 ∨ 1 ≤ x) :
    1 / 2 * hFun σ ξ α e x ≤ dosCost σ ξ α e x ∧
      dosCost σ ξ α e x ≤
        max (qPar σ ξ α e) 1 * (ξ e * qPar σ ξ α e ^ (α e - 1)) * x + ξ e * x ^ α e ∧
      max (qPar σ ξ α e) 1 * (ξ e * qPar σ ξ α e ^ (α e - 1)) * x + ξ e * x ^ α e ≤
        max (qPar σ ξ α e) 1 * hFun σ ξ α e x := by sorry

end OnlineGND
