-- Prove2me | Theorems.Thm_MultistageRUC_Equiv_theorem_1
-- name    : MultistageRUC.Equiv.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:58.999458+00:00
-- url     : https://prove2.me/theorems/7d7d8065-5f20-4c65-85f1-6efa7fea7b90
-- title:
--   Theorem 1, p. 11 — without ramping constraints, the two-stage robust UC (2) and the multistage robust UC (5) are equivalent
-- statement:
--   Consider the unit commitment problem with budget uncertainty set $\mathcal D=\prod_t\mathcal D^t$ of (3), with $\Gamma\ge0$ and $\hat d_j^t>0$. Delete the ramping constraints, (1i) in the two-stage robust UC (2) and (5c) in the multistage robust UC (5). Then the two models are equivalent:
--
--   1. at every commitment $(x,u,v)\in X$ they have the same objective value,
--   $$F(x)+\max_{d\in\mathcal D}\ \min_{p\in\Omega^{NR}(x,d)}c(p)\;=\;F(x)+\min_{p(\cdot)}\ \max_{d\in\mathcal D}\sum_{t\in\mathcal T}\sum_{i\in\mathcal N_g}C_ip_i^t(d^{[t]}),$$
--   where the minimum on the right is over non-anticipative dispatch policies $p^t(d^{[t]})$, depending only on the net loads $d^1,\dots,d^t$ realized up to period $t$, that satisfy (5b), (5d), (5e) for every $d\in\mathcal D$;
--   2. hence their optimal values over $X$ coincide.
--
--   The two-stage model lets the dispatch see the whole day's net loads; the multistage model does not. The theorem says that this extra information is worthless when the ramping constraints are absent, so the multistage model differs from the two-stage model only through ramping; Propositions 1 and 2 show that with ramping the two models can differ.
--
--   **Formalization Note** Periods are `Fin T` with Lean period $t$ being the paper's period $t+1$. Net-load trajectories are $d:\{0,\dots,T-1\}\to\mathbb R^{N_d}$. Values are extended reals: a minimum over an empty set is $+\infty$ (an infeasible dispatch problem costs $+\infty$). The standing assumptions $\Gamma\ge 0$ and $\hat d^t_j>0$ of the budget set (3) are carried as hypotheses; they make $\bar d\in\mathcal D$, so every $\mathcal D^t$ is nonempty. "Equivalent" is formalized as equality of the two objectives at every commitment in $X$ together with equality of the optimal values; equal objectives on $X$ also give the same optimal solutions.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 11, Theorem 1

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.Equiv

/-- Theorem 1, p. 11: without ramping constraints (5c), the two-stage robust UC (2) and the multistage
robust UC (5) are equivalent: they have the same objective value at every commitment `(x, u, v) ∈ X`,
and hence the same optimal value. -/
theorem theorem_1 {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j) :
    (∀ x u v : Fin Ng → Fin T → ℝ, InX D x u v →
      twoStageObj D (uncSet dbar dhat Γ) false x u v =
        multiStageObj D (uncSet dbar dhat Γ) false x u v) ∧
    (⨅ (x : Fin Ng → Fin T → ℝ) (u : Fin Ng → Fin T → ℝ) (v : Fin Ng → Fin T → ℝ)
        (_ : InX D x u v), twoStageObj D (uncSet dbar dhat Γ) false x u v) =
      (⨅ (x : Fin Ng → Fin T → ℝ) (u : Fin Ng → Fin T → ℝ) (v : Fin Ng → Fin T → ℝ)
        (_ : InX D x u v), multiStageObj D (uncSet dbar dhat Γ) false x u v) := by sorry

end MultistageRUC.Equiv
