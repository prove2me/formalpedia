-- Prove2me | Theorems.Thm_Micromobility_Transient_lemma_H_9
-- name    : Micromobility.Transient.lemma_H_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:21.962695+00:00
-- url     : https://prove2.me/theorems/dc2c4efc-f8f8-444b-8a39-ddd46f2858dc
-- title:
--   Lemma H.9, p. A-33 — ĉ₂ between two actions is at most Σₑ(nₑ max(c₀ₑ, cₑ₀)(Uᵉ − Lᵉ) + n max(c₀,ê₊ₑ, cê₊ₑ,₀)(U^{r,e} − L^{r,e}))
-- statement:
--   Under the standing assumptions, for any two actions $\hat a^1, \hat a^2 \in \hat A$,
--   $$\hat c_2(\hat a^1, \hat a^2) \le \sum_{e=1}^{\hat e}\Big(n_e\max(c_{0,e}, c_{e,0})(U^e - L^e) + n\max(c_{0,\hat e+e}, c_{\hat e+e,0})(U^{r,e} - L^{r,e})\Big),$$
--   where $\hat a^1$ is read as a state (p. A-31).
--
--   The right-hand side is half of Theorem 4.2's constant $C$: it bounds the cost of moving between any two feasible post-rebalancing distributions by routing every excess or deficit through the warehouse.
--
--   **Formalization Note.** The standing assumptions include $c_{e_1,e_2} \ge 0$, which the paper uses implicitly; without it the right-hand side could be negative while $\hat c_2(\hat a, \hat a) = 0$.
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), p. A-33, Lemma H.9

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting

namespace Micromobility.Transient
theorem lemma_H_9 {ê : ℕ} (M : Model ê) (hM : M.Standing)
    (a₁ a₂ : Action ê) (h₁ : M.InA a₁) (h₂ : M.InA a₂) :
    M.c2 (toState a₁) a₂ ≤
      ∑ e, ((M.nst e : ℝ) * max (M.c 0 (chg e)) (M.c (chg e) 0) * ((M.U e : ℝ) - (M.L e : ℝ))
      + M.n * max (M.c 0 (dep e)) (M.c (dep e) 0) * (M.Ur e - M.Lr e)) := by sorry
end Micromobility.Transient
