-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem52
-- name    : NegativeDP.EssFinite.Supplement.theorem52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:55:20.494161+00:00
-- url     : https://prove2.me/theorems/b9f76b5f-92bd-48c9-80f9-c18dcd26735f
-- title:
--   Theorem 5.2 (D: a–f; P: a–g) — properties of U; D(g) is DiscountedDP.Stationary.theorem4d_generated_selection
-- statement:
--   Let $\pi=(f_1,f_2,\dots)$ be a Markov policy, $T_n$ the operator of $f_n$ and $Uu=\sup_nT_nu$, acting on $M(S)$, the bounded Borel functions. In the discounted case and in the positive bounded case:
--
--   1. (a) $U$ is monotone: $u\le v$ implies $Uu\le Uv$.
--   2. (b) $U(u+c)=Uu+\beta c$ for every constant $c$.
--   3. (c) $U(\sup_j u_j)\ge\sup_j Uu_j$.
--   4. (d) If $u_j\downarrow u$ then $\inf_jUu_j\ge Uu$, and if $u_j\uparrow u$ then $\sup_jUu_j\le Uu$, with equality on $\{\sup_jT_nu_j>-\infty\text{ for all }n\}$, which in these cases is all of $S$:
--
--   $$
--   \sup_j Uu_j=Uu .
--   $$
--
--   5. (e) D: $U$ is a contraction, $\|Uu-Uv\|\le\beta\|u-v\|$; P: $U$ is positive.
--   6. (f) For every $\pi$-generated $f$ with operator $T$ and every $u\in M(S)$, $Tu\le Uu$.
--   7. (g) For every $u\in M(S)$ and $\varepsilon>0$ there is a $\pi$-generated $f$ whose operator satisfies $Tu\ge Uu-\varepsilon$.
--
--   A rule $f$ is $\pi$-generated if $f=f_n$ on $S_n$ for a partition of $S$ into Borel sets $S_1,S_2,\dots$. The item states (a)–(f) in case D and (a)–(g) in case P; clause (g) in case D is the published Blackwell item `DiscountedDP.Stationary.theorem4d_generated_selection`, included in this mission as a reference. The negative case of this theorem is the published items `NegativeDP.OptEq.theorem52a`, `NegativeDP.OptEq.theorem52b`, `NegativeDP.OptEq.theorem52c`, `NegativeDP.OptEq.theorem52d`, `NegativeDP.OptEq.theorem52e`, `NegativeDP.OptEq.theorem52f`, `NegativeDP.OptEq.theorem52g`; together with this item it covers the whole source theorem. These properties are used throughout §6 and §8.
--
--   **Formalization Note** The first conjunct is case D with Blackwell's `U`, `T`, `IsGenerated`, `supNorm`; the second is case P with `Pos.U`, `Pos.T`. $M(S)$ is `IsBM`. In (d) the limit $u$ is assumed in $M(S)$, $u_j\downarrow u$ is `Antitone` plus pointwise convergence, and both the inequality and the equality of the increasing case are stated.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.OptEq.theorem52a, theorem52b, theorem52c, theorem52d, theorem52e, theorem52f, theorem52g; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - encoding: clause (g) in case D → not restated; it is the published reference DiscountedDP.Stationary.theorem4d_generated_selection (same statement, same model); reason: avoids a duplicate of a published theorem
--   - reading: T(supⱼ uⱼ) for uⱼ ∈ M(S), T an operator on M(S) → uⱼ bounded Borel with a common upper bound C; reason: this is exactly the condition supⱼ uⱼ ∈ M(S) (bounded below by u₀, measurable as a countable supremum), which the paper needs for T(supⱼ uⱼ) to be defined
--   - reading: (d): uⱼ ↓ u, uⱼ ↑ u for uⱼ ∈ M(S) → the limit u is also in M(S) (IsBM u); reason: Uu is only defined for u ∈ M(S); a decreasing limit of bounded functions need not be bounded below
--   - encoding: (d): equality on {supⱼ Tₙuⱼ > −∞ for all n} → equality at every state; reason: in cases D and P every Tₙuⱼ is real, so the set is all of S
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 879, Theorem 5.2

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 5.2 (p. 879), discounted case clauses (a)–(f) (first conjunct) and positive bounded
case clauses (a)–(g) (second conjunct), on `M(S)` = bounded Borel functions, for the operator
`Uu = supₙ Tₙu` of a Markov plan `π`:
(a) `U` is monotone; (b) `U(u + c) = Uu + βc`; (c) `U(supⱼ uⱼ) ≥ supⱼ Uuⱼ` (for `supⱼ uⱼ ∈ M(S)`);
(d) `uⱼ ↓ u` implies `infⱼ Uuⱼ ≥ Uu`; `uⱼ ↑ u` implies `supⱼ Uuⱼ ≤ Uu`, with equality on
`{supⱼ Tₙuⱼ > −∞ for all n}`, which is all of `S` in these cases;
(e) D: `‖Uu − Uv‖ ≤ β‖u − v‖`; P: `u ≥ 0` implies `Uu ≥ 0`;
(f) `Tu ≤ Uu` for every `π`-generated `f`;
(g) for `u ∈ M(S)` and `ε > 0` some `π`-generated `f` has `Tu ≥ Uu − ε`.
Clause (g) in case D is the published Blackwell item
`DiscountedDP.Stationary.theorem4d_generated_selection`; the negative case is the published
`NegativeDP.OptEq.theorem52a`–`theorem52g`. -/
theorem theorem52 :
    (∀ (P : Problem S A) (π : MarkovPlan S A),
      (∀ u v : S → ℝ, IsBM u → IsBM v → (∀ s, u s ≤ v s) → ∀ s, U P π u s ≤ U P π v s) ∧
      (∀ (u : S → ℝ) (c : ℝ), IsBM u → ∀ s, U P π (fun t => u t + c) s = U P π u s + P.β * c) ∧
      (∀ uj : ℕ → S → ℝ, (∀ j, IsBM (uj j)) → (∃ C : ℝ, ∀ j s, uj j s ≤ C) →
        ∀ s, (⨆ j, U P π (uj j) s) ≤ U P π (fun t => ⨆ j, uj j t) s) ∧
      (∀ (uj : ℕ → S → ℝ) (u : S → ℝ), (∀ j, IsBM (uj j)) → IsBM u →
        ((Antitone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          ∀ s, U P π u s ≤ ⨅ j, U P π (uj j) s) ∧
        ((Monotone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          (∀ s, (⨆ j, U P π (uj j) s) ≤ U P π u s) ∧ ∀ s, (⨆ j, U P π (uj j) s) = U P π u s)) ∧
      (∀ u v : S → ℝ, IsBM u → IsBM v →
        supNorm (fun s => U P π u s - U P π v s) ≤ P.β * supNorm (fun s => u s - v s)) ∧
      (∀ (f : {g : S → A // Measurable g}), IsGenerated π f →
        ∀ u : S → ℝ, IsBM u → ∀ s, T P f u s ≤ U P π u s)) ∧
    (∀ (P : Pos.Problem S A) (π : MarkovPlan S A),
      (∀ u v : S → ℝ, IsBM u → IsBM v → (∀ s, u s ≤ v s) → ∀ s, Pos.U P π u s ≤ Pos.U P π v s) ∧
      (∀ (u : S → ℝ) (c : ℝ), IsBM u → ∀ s, Pos.U P π (fun t => u t + c) s = Pos.U P π u s + c) ∧
      (∀ uj : ℕ → S → ℝ, (∀ j, IsBM (uj j)) → (∃ C : ℝ, ∀ j s, uj j s ≤ C) →
        ∀ s, (⨆ j, Pos.U P π (uj j) s) ≤ Pos.U P π (fun t => ⨆ j, uj j t) s) ∧
      (∀ (uj : ℕ → S → ℝ) (u : S → ℝ), (∀ j, IsBM (uj j)) → IsBM u →
        ((Antitone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          ∀ s, Pos.U P π u s ≤ ⨅ j, Pos.U P π (uj j) s) ∧
        ((Monotone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          (∀ s, (⨆ j, Pos.U P π (uj j) s) ≤ Pos.U P π u s) ∧
            ∀ s, (⨆ j, Pos.U P π (uj j) s) = Pos.U P π u s)) ∧
      (∀ u : S → ℝ, IsBM u → (∀ s, 0 ≤ u s) → ∀ s, 0 ≤ Pos.U P π u s) ∧
      (∀ (f : {g : S → A // Measurable g}), IsGenerated π f →
        ∀ u : S → ℝ, IsBM u → ∀ s, Pos.T P f u s ≤ Pos.U P π u s) ∧
      (∀ u : S → ℝ, IsBM u → ∀ ε : ℝ, 0 < ε →
        ∃ f : {g : S → A // Measurable g}, IsGenerated π f ∧
          ∀ s, Pos.U P π u s - ε ≤ Pos.T P f u s)) := by sorry

end NegativeDP.EssFinite.Supplement
