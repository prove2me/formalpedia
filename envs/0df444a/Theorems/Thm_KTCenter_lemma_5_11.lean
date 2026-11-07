-- Prove2me | Theorems.Thm_KTCenter_lemma_5_11
-- name    : KTCenter.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:14.145508+00:00
-- url     : https://prove2.me/theorems/17f064a4-28d3-45b8-8040-82767ee20e8b
-- title:
--   Lemma 5.11 — expected costs of LP solutions (64) and feasibility of (LP1) with value $\le\max_i\tilde C_i(\varphi\cup p^*)+\Delta$ (65)
-- statement:
--   Let $I$ be a cost instance with positive constants $C_0,C_1$, $0<\xi<1$, $\varphi\in\mathcal P(F)$, $g$ a large-subset member (sample sequences with guesses for every large block) and $(G_B)_{B\in\mathcal B_s}$ small-subset families. Then:
--
--   1. for every feasible solution of (LP1) and every $i$,
--   $$\Bigl|\mu_i-\Bigl(A'_i+H^g_i(x)+\sum_{B\in\mathcal B_s}\sum_{h\in G_B}H_{iB,h}(y^{Bh})\Bigr)\Bigr|\le\Delta,\qquad(64)$$
--   where $\mu_i$ is the expected surrogate cost under the rounding distribution of the solution, and $\Delta\le\gamma W/2$;
--   2. for every $p^*\in\mathcal P(U')$: if the guesses of $g$ agree with $p^*$ and satisfy (45), and every $G_B$ contains a member whose guesses agree with $p^*$ and which satisfies (54), then (LP1) is feasible and its optimum value $t_{LP}$ exists and satisfies
--   $$t_{LP}\le\max_{i\in[n]}\tilde C_i(\varphi\cup p^*)+\Delta.\qquad(65)$$
--
--   Differences from the source:
--
--   - generalization: random samples, G_B = 𝒫(S_B), U′ ≠ ∅ → arbitrary sample sequences, guesses and small-subset lists; U′ = ∅ allowed; reason: the proof uses only the constraints and (45), (54); §6 applies the lemma to walk-based families; it specializes to the source
--   - reading: "If (45) and (54) hold for p*" with g* = p*|_{S_ℓ} and h*_B = p*|_{S_B} → g agrees with p* and satisfies (45); each G_B contains a member agreeing with p* and satisfying (54); reason: this is what the source's g*, h*_B are
--   - encoding: µ_i = E[C̃_i(p)] → finite sum over outcomes of the rounding distribution; reason: Lean convention; same value
--   - encoding: "its optimum objective" → IsLeast of the set of feasible values t; reason: the minimum exists, as p.50 states
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 5.11, eqs. (64)–(65), pp.49–50 (PDF pp.51–52)

import Mathlib
import Definitions.Def_KTCenter_CostInstance
import Definitions.Def_KTCenter_FixKeys
import Definitions.Def_KTCenter_LP1
import Definitions.Def_KTCenter_Rounding

namespace KTCenter

/-- **Lemma 5.11** (LP feasibility and expected costs), eqs. (64), (65), pp.49–50 (PDF pp.51–52).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** For arbitrary sample sequences and guesses: nothing in the lemma uses their
law, so "before drawing the samples" adds nothing. `µᵢ` is computed from the distribution of p.49 as a
finite sum. `K, C₀` are as in the instance. "Its optimum objective" is `IsLeast`, so (65) contains that
the minimum exists. -/
theorem lemma_5_11 {K : ℕ} {C₀ C₁ : ℚ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (I : CostInstance K C₀ C₁) (ξ : ℚ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (φ : I.AssignOn (I.F ξ)) (g : I.LargeMember ξ) (fam : I.SmallFamily ξ) :
    (∀ P : I.LPPoint ξ fam, CostInstance.IsFeasible φ g P → ∀ i : Fin I.n,
      |CostInstance.mu φ P i - CostInstance.lpCost φ g P i| ≤ (I.Delta ξ : ℝ)) ∧
    I.Delta ξ ≤ CostInstance.gamma ξ * I.W / 2 ∧
    ∀ pstar : I.AssignOn (I.Ures ξ),
      (∀ B, (g B).AgreesWith pstar) →
      CostInstance.Cond45 g pstar →
      (∀ B : {B // B ∈ I.bSmall ξ}, ∃ h : Fin (fam B).length,
        ((fam B).get h).AgreesWith pstar ∧ CostInstance.Cond54 ((fam B).get h) pstar) →
      ∃ tLP : ℝ,
        IsLeast {t : ℝ | ∃ P : I.LPPoint ξ fam, CostInstance.IsFeasible φ g P ∧ P.t = t} tLP ∧
        tLP ≤ ((I.maxCost (I.union ξ φ pstar) + I.Delta ξ : ℚ) : ℝ) := by sorry

end KTCenter
