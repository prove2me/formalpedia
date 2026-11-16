-- Prove2me | Theorems.Thm_LearnVsOpt_Supplement_theorem_7_4
-- name    : LearnVsOpt.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:23:38.714054+00:00
-- url     : https://prove2.me/theorems/d1952806-5e39-4015-9867-1ad9d3af7520
-- title:
--   Theorem 7.4, p.25 — a two-phase stationary optimizer secures the weak BSE against any low-regret learner
-- statement:
--   Let $\rho_L,\rho_O\in(0,1]$, and let the learner have a null action $j_0$ with $C_L[\cdot,j_0]=0$.
--
--   **(1)** Fix any feasible solution $(x_1,x_2,q)$ to (28) and let $\Delta=\min\{\Delta(x_1),\Delta(x_2)\}$, with $\Delta(\cdot)$ the vertex suboptimality gap (29). Suppose the optimizer plays $i_t\sim x_1$ independently in the first $T_1=\lfloor qT\rfloor$ rounds ($\mathcal I_1=\{1,\dots,T_1\}$) and $i_t\sim x_2$ in the remaining rounds ($\mathcal I_2=\{T_1+1,\dots,T\}$). Its opponent is any learning algorithm whose expected stochastic regret and expected overspending on $\mathcal I_s$ are at most $\mathrm{Reg}_{\mathcal I_s}\ge0$ and $\mathrm{Over}_{\mathcal I_s}\ge0$. Let $\mathrm{Reg}=\mathrm{Reg}_{\mathcal I_1}+\mathrm{Reg}_{\mathcal I_2}$ and $\mathrm{Over}=\mathrm{Over}_{\mathcal I_1}+\mathrm{Over}_{\mathcal I_2}$. Then
--   $$\mathbb E\Big[\sum_{t=1}^T U_O[i_t,j_t]\Big]\ge\Big(q\min_{y_1\in \mathrm{BR}_L(x_1)}x_1^\top U_O y_1+(1-q)\min_{y_2\in \mathrm{BR}_L(x_2)}x_2^\top U_O y_2\Big)T-\frac{\mathrm{Reg}+2\,\mathrm{Over}/\rho_L}{\Delta}-1,$$
--   $$\mathbb E\Big[\sum_{t=1}^T C_O[i_t,j_t]\Big]\le\rho_O T+\frac{\mathrm{Reg}+2\,\mathrm{Over}/\rho_L}{\Delta}+1.$$
--
--   **(2) Consequently.** Suppose the optimizer has a null action $i_0$ with $C_O[i_0,\cdot]=0$, and let $r(T)=o(T)$. Then there are optimizers $\xi_T$, each stationary on at most three contiguous intervals partitioning $[T]$ and chosen from $r$ alone, with the following property. Against every learning algorithm whose expected regret and expected overspending are at most $r(T)$ on every phase of every such three-phase optimizer, $\xi_T$ has expected cost at most $\rho_O T$ for every $T$, and expected utility at least $\mathrm{WBSE}\cdot T-o(T)$: for every $\varepsilon>0$ it is at least $(\mathrm{WBSE}-\varepsilon)T$ for all large $T$, uniformly in the learner.
--
--   The theorem lower-bounds what a budgeted optimizer can extract from any learner with sublinear regret and overspending, Algorithms 1 and 2 included.
--
--   **Formalization Note** A learning algorithm is a kernel from the past actions to the law of the learner's next action. Optimizers that ignore the learner draw $i_t\sim\xi(t)$, with $\xi(t)$ a law on $[n_O]$.
--
--   Differences from the source:
--   - reading: a learning algorithm with stochastic regret Reg_{I_s} and overspending Over_{I_s} on each phase → any reals Reg_s, Over_s ≥ 0 bounding |I_s|V_L(x_s) − E[Σ_{I_s} U_L] and E[Σ_{I_s} C_L] − ρ_L|I_s|; reason: Theorem 7.4 applies Lemma 7.3, whose hypotheses are exactly these (p.24)
--   - encoding: any learning algorithm → any kernel from the past (i_r, j_r)_{r<t} to PMF (Fin n_L); reason: against an oblivious optimizer the joint law of play of any learner is of this form; no budget constraint is imposed
--   - encoding: x₁, x₂ ∈ Δ_{n_O}; I₁ = {1, …, T₁}, T₁ = ⌊qT⌋ → x₁, x₂ laws on [n_O] read as vectors by toVec; Finset.Icc 1 ⌊q T⌋₊ and Finset.Ioc ⌊q T⌋₊ T; reason: every point of Δ_{n_O} is a law; the same intervals
--   - encoding: the max and min in (28)–(29); 𝒱(x) the vertex set of 𝓕(x) → sSup / sInf of value sets; Set.extremePoints ℝ (𝓕(x)); reason: the sets are nonempty compact (finite for the vertices), so the values are attained
--   - reading: Consequently, whenever Reg, Over = o(T), by taking (x₁, x₂, q) approaching the supremum in (28) (and shortening the active phases by O((Reg+Over/ρ_L+1)/(ρ_O Δ)) rounds of the optimizer's null action), the optimizer achieves expected utility at least WBSE · T − o(T) → given an optimizer null action i₀ (C_O[i₀, ·] = 0) and r(T) with r(T)/T → 0, there are optimizers ξ_T with at most three stationary phases partitioning [T], depending only on r, such that for every learner A whose expected regret and overspending are ≤ r(T) on every phase of every such optimizer (IsLowRegret), E[Σ_t C_O] ≤ ρ_O T for every T, and for every ε > 0, for all large T and every such A, E[Σ_t U_O] ≥ (WBSE − ε)T; reason: the learner's regret must be o(T) uniformly over the shortened optimizers, which removes the circularity of the sentence; the optimizer is fixed before the learner, as in the theorem, where the strategy depends only on the bounds Reg, Over; the budget is in expectation, as in the base goal's clause (c), since the argument controls only expected cost; three phases are the two phases and the null padding
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Theorem 7.4, p.25 (PDF p.26); (28)–(29) and Lemma 7.3, p.24

import Mathlib
import Definitions.Def_LearnVsOpt_Supplement_Weak

set_option autoImplicit false

open Filter Topology
open scoped Matrix

namespace LearnVsOpt.Supplement

/-- **Theorem 7.4** (Fikioris, Sivan & Tardos, *Learning vs. Optimizing Players in Budgeted Games*,
arXiv:2611.05580, Theorem 7.4, p.25). Fix any feasible solution `(x₁, x₂, q)` to (28) and let
`Δ = min{Δ(x₁), Δ(x₂)}`. If the optimizer plays `i_t ∼ x₁` for the first `T₁ = ⌊qT⌋` rounds and
`i_t ∼ x₂` for the remaining `T₂ = T − T₁` rounds against any learning algorithm with stochastic regret
`Reg_{I_s}` and overspending `Over_{I_s}` on each phase, then (with `Reg = Reg_{I₁} + Reg_{I₂}`,
`Over = Over_{I₁} + Over_{I₂}`)
`E[Σ_t U_O[i_t, j_t]] ≥ (q min_{BR_L(x₁)} x₁⊤U_O y₁ + (1 − q) min_{BR_L(x₂)} x₂⊤U_O y₂) T − (Reg + 2 Over/ρ_L)/Δ − 1`
and `E[Σ_t C_O[i_t, j_t]] ≤ ρ_O T + (Reg + 2 Over/ρ_L)/Δ + 1`. Consequently, whenever `Reg, Over = o(T)`,
the optimizer achieves expected utility at least `WBSE · T − o(T)`.

**Formalization Note.** Clause 1 is the two inequalities, with `Reg_{I_s}, Over_{I_s} ≥ 0` any upper
bounds on the expected regret and overspending (Lemma 7.3, p.24). Clause 2 is the "Consequently"
sentence: for every rate `r(T) = o(T)` there are optimizers `ξ_T` with at most three stationary phases
(the two phases and the null-action padding), chosen from `r` alone, such that against every learner
whose regret and overspending are at most `r(T)` on every phase of every such optimizer
(`IsLowRegret`), the expected cost is within `ρ_O T`, and the expected utility is at least
`(WBSE − ε) T` for every `ε > 0` and all large `T`, uniformly in the learner. The optimizer's mixed strategies are laws on `[n_O]` (`toVec` reads the vector). -/
theorem theorem_7_4 {nO nL : ℕ} (G : Game nO nL) (ρL ρO : ℝ) (hρL₀ : 0 < ρL) (hρL₁ : ρL ≤ 1)
    (hρO₀ : 0 < ρO) (hρO₁ : ρO ≤ 1) (j₀ : Fin nL) (hj₀ : ∀ i, G.CL i j₀ = 0) :
    (∀ (x₁ x₂ : PMF (Fin nO)) (q : ℝ), IsWBSEFeasible G ρL ρO (toVec x₁) (toVec x₂) q →
      ∀ (T : ℕ) (A : Learner nO nL) (Reg₁ Reg₂ Over₁ Over₂ : ℝ),
        0 ≤ Reg₁ → 0 ≤ Reg₂ → 0 ≤ Over₁ → 0 ≤ Over₂ →
        regretOn G ρL (oblLaw (twoPhase ⌊q * T⌋₊ x₁ x₂) A T) (Finset.Icc 1 ⌊q * T⌋₊) (toVec x₁)
          ≤ Reg₁ →
        regretOn G ρL (oblLaw (twoPhase ⌊q * T⌋₊ x₁ x₂) A T) (Finset.Ioc ⌊q * T⌋₊ T) (toVec x₂)
          ≤ Reg₂ →
        overOn G ρL (oblLaw (twoPhase ⌊q * T⌋₊ x₁ x₂) A T) (Finset.Icc 1 ⌊q * T⌋₊) ≤ Over₁ →
        overOn G ρL (oblLaw (twoPhase ⌊q * T⌋₊ x₁ x₂) A T) (Finset.Ioc ⌊q * T⌋₊ T) ≤ Over₂ →
        (q * minUO G ρL (toVec x₁) + (1 - q) * minUO G ρL (toVec x₂)) * T -
            ((Reg₁ + Reg₂) + 2 * (Over₁ + Over₂) / ρL) /
              min (gap G ρL (toVec x₁)) (gap G ρL (toVec x₂)) - 1 ≤
          expect (oblLaw (twoPhase ⌊q * T⌋₊ x₁ x₂) A T)
            (fun ω => ∑ t ∈ Finset.Icc 1 T, pathEntry ω G.UO t) ∧
        expect (oblLaw (twoPhase ⌊q * T⌋₊ x₁ x₂) A T)
            (fun ω => ∑ t ∈ Finset.Icc 1 T, pathEntry ω G.CO t) ≤
          ρO * T + ((Reg₁ + Reg₂) + 2 * (Over₁ + Over₂) / ρL) /
              min (gap G ρL (toVec x₁)) (gap G ρL (toVec x₂)) + 1) ∧
    ((∃ i₀, ∀ j, G.CO i₀ j = 0) →
      ∀ r : ℕ → ℝ, Tendsto (fun T : ℕ => r T / T) atTop (𝓝 0) →
        ∃ ξ : ℕ → OblOpt nO,
          (∀ T : ℕ, ∃ (a b : ℕ) (x₁ x₂ x₃ : PMF (Fin nO)), IsThreePhase (ξ T) T a b x₁ x₂ x₃) ∧
          (∀ (T : ℕ) (A : Learner nO nL), IsLowRegret G ρL T A (r T) →
            expect (oblLaw (ξ T) A T) (fun ω => ∑ t ∈ Finset.Icc 1 T, pathEntry ω G.CO t) ≤ ρO * T) ∧
          ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, ∀ A : Learner nO nL, IsLowRegret G ρL T A (r T) →
            (WBSE G ρL ρO - ε) * T ≤
              expect (oblLaw (ξ T) A T) (fun ω => ∑ t ∈ Finset.Icc 1 T, pathEntry ω G.UO t)) := by sorry

end LearnVsOpt.Supplement
