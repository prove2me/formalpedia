-- Prove2me | Theorems.Thm_LearnVsOpt_Supplement_theorem_7_5
-- name    : LearnVsOpt.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:24:30.204358+00:00
-- url     : https://prove2.me/theorems/6fbd8aa3-2b0c-4d91-a142-4f1bfd601fcc
-- title:
--   Theorem 7.5, p.25 — WBSE = BSE for generic learner utilities and costs
-- statement:
--   Fix $n_O,n_L$, the learner's null action $j_0\in[n_L]$, budgets $\rho_L,\rho_O\in(0,1]$, and the optimizer's utility and cost matrices $U_O,C_O\in[0,1]^{n_O\times n_L}$, where the optimizer has an action $i_0$ with $C_O[i_0,\cdot]=0$. Call a property of the learner's matrices **generic** (Appendix H) if it holds for all $(U_L,C_L)\in[0,1]^{n_O\times n_L}\times[0,1]^{n_O\times n_L}$ with $U_L[\cdot,j_0]=C_L[\cdot,j_0]=0$, except on a set of Lebesgue measure zero in the unrestricted entries $[n_O]\times([n_L]\setminus\{j_0\})$. Then for generic learner utilities and costs $(U_L,C_L)$,
--   $$\mathrm{WBSE}=\mathrm{BSE},$$
--   where $\mathrm{BSE}$ is the two-phase budgeted Stackelberg value (26) (optimistic tie-breaking) and $\mathrm{WBSE}$ is its pessimistic counterpart (28).
--
--   Together with Theorem 7.4, this shows that in generic games the budgeted optimizer can reach the strong value $\mathrm{BSE}$ against any low-regret learner. The non-manipulability guarantee of the goal is therefore tight.
--
--   **Formalization Note** The almost-everywhere quantifier is over the Lebesgue measure on the pairs of free-entry arrays, with the condition that all entries lie in $[0,1]$ as a hypothesis inside it.
--
--   Differences from the source:
--   - encoding: for generic (U_L, C_L) (Appendix H, p.40: outside a Lebesgue-null set of the unrestricted entries [n_O] × ([n_L] ∖ {j₀}), with U_L[·, j₀] = C_L[·, j₀] = 0) → ∀ᵐ (U′, C′) on (Fin n_O → {j // j ≠ j₀} → ℝ)², all entries in [0, 1] → WBSE = BSE₂ for learnerGame, with columns j₀ set to 0; reason: Appendix H's definition
--   - encoding: BSE in Theorem 7.5 → Game.BSE₂ ρ_L ρ_O, the two-phase budgeted value (26); reason: WBSE (28) is (26) with pessimistic tie-breaking, and Appendix H's proof compares them
--   - encoding: the optimizer's null action i₀ and ρ_L, ρ_O ∈ (0, 1] (§2, §7) → U_O, C_O ∈ [0, 1], ∃ i₀, ∀ j, C_O i₀ j = 0, ρ_L, ρ_O ∈ (0, 1], all fixed before the almost-everywhere quantifier; reason: standing assumptions; the proof on p.43 uses i₀
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Theorem 7.5, p.25 (PDF p.26); Appendix H, pp.40–43 (PDF pp.41–44)

import Mathlib
import Definitions.Def_LearnVsOpt_Supplement_Weak

set_option autoImplicit false

open MeasureTheory

namespace LearnVsOpt.Supplement

/-- **Theorem 7.5** (Fikioris, Sivan & Tardos, *Learning vs. Optimizing Players in Budgeted Games*,
arXiv:2611.05580, Theorem 7.5, p.25; Appendix H, pp.40–43). For generic learner utilities and costs
`(U_L, C_L)`, it holds that `WBSE = BSE`.

**Formalization Note.** "Generic" is Appendix H's definition (p.40): for all
`(U_L, C_L) ∈ [0,1]^{n_O×n_L} × [0,1]^{n_O×n_L}` with `U_L[·, j₀] = C_L[·, j₀] = 0`, outside a Lebesgue-null
set of the unrestricted entries `[n_O] × ([n_L] \ {j₀})`. The optimizer's `U_O`, `C_O` (with a zero-cost
action `i₀`), `ρ_L` and `ρ_O` are fixed first. `BSE` is the two-phase budgeted value (26),
`LearnVsOpt.Game.BSE₂`, and `WBSE` is (28). -/
theorem theorem_7_5 {nO nL : ℕ} (UO CO : Matrix (Fin nO) (Fin nL) ℝ)
    (hUO : ∀ i j, UO i j ∈ Set.Icc (0 : ℝ) 1) (hCO : ∀ i j, CO i j ∈ Set.Icc (0 : ℝ) 1)
    (j₀ : Fin nL) (hi₀ : ∃ i₀, ∀ j, CO i₀ j = 0) (ρL ρO : ℝ) (hρL₀ : 0 < ρL) (hρL₁ : ρL ≤ 1)
    (hρO₀ : 0 < ρO) (hρO₁ : ρO ≤ 1) :
    ∀ᵐ p : (Fin nO → {j : Fin nL // j ≠ j₀} → ℝ) × (Fin nO → {j : Fin nL // j ≠ j₀} → ℝ),
      ∀ (hU : ∀ i j, p.1 i j ∈ Set.Icc (0 : ℝ) 1) (hC : ∀ i j, p.2 i j ∈ Set.Icc (0 : ℝ) 1),
        WBSE (learnerGame UO CO hUO hCO j₀ p.1 p.2 hU hC) ρL ρO =
          (learnerGame UO CO hUO hCO j₀ p.1 p.2 hU hC).BSE₂ ρL ρO := by sorry

end LearnVsOpt.Supplement
