-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem51
-- name    : NegativeDP.EssFinite.Supplement.theorem51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:54:39.251775+00:00
-- url     : https://prove2.me/theorems/592a5413-5a5e-432e-87cb-78ecdb2ccf5d
-- title:
--   Theorem 5.1 (D, P) — properties (a)–(g) of the one-rule operator T
-- statement:
--   Let $f:S\to A$ be measurable and $T$ its operator, $Tu(s)=\int r(s,f(s),t)+\beta u(t)\,dq(t\mid s,f(s))$, acting on $M(S)$, the bounded Borel functions. In the discounted case ($0\le\beta<1$) and in the positive bounded case ($\beta=1$):
--
--   1. (a) $T$ is monotone: $u\le v$ implies $Tu\le Tv$.
--   2. (b) $T(u+c)=Tu+\beta c$ for every constant $c$.
--   3. (c) $T(\sup_j u_j)\ge\sup_j Tu_j$.
--   4. (d) If $u_j\downarrow u$ then $Tu_j\downarrow Tu$, and if $u_j\uparrow u$ then $Tu_j\uparrow Tu$.
--   5. (e) D: $T$ is a contraction, $\|Tu-Tv\|\le\beta\|u-v\|$; P: $T$ is positive, $u\ge0$ implies $Tu\ge0$.
--   6. (f) For every policy $\pi$, $TI(\pi)=I(f,\pi)$, where $(f,\pi)=(f,\pi_1,\pi_2,\dots)$ uses $f$ and then $\pi$. In particular
--
--   $$
--   TI(f^{(\infty)})=I(f^{(\infty)})=\lim_{n\to\infty}T^n0.
--   $$
--
--   7. (g) If $\pi=\{f_1,f_2,\dots\}$ is Markov and $T_n$ is the operator of $f_n$, then $I_n(\pi,v)=T_1\cdots T_nv$.
--
--   The negative case of this theorem is the published items `NegativeDP.Stationary.theorem51a`, `NegativeDP.Stationary.theorem51bce`, `NegativeDP.Stationary.theorem51d`, `NegativeDP.Stationary.theorem51f`, `NegativeDP.Stationary.theorem51g`; together with this item it covers the whole source theorem. These are the operator facts on which every later section rests.
--
--   **Formalization Note** The first conjunct is case D with Blackwell's `T`, `I`, `supNorm`; the second is case P with `Pos.T`, `Pos.I`, `Pos.In`. $M(S)$ is `IsBM` (bounded and Borel). In (d), $u_j\downarrow u$ is `Antitone` plus pointwise convergence to $u\in M(S)$, and the convergence of $Tu_j$ is stated at every state. In (f), `prefixPlan f π` (published) is $(f,\pi)$ and `stationary f` is $f^{(\infty)}$; $T^n0$ is `(T P f)^[n] 0`. In (g) the rules are `m 0, m 1, …` and $T_1\cdots T_nv$ is the right fold over `0, …, n − 1`.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.Stationary.theorem51a, theorem51bce, theorem51d, theorem51f, theorem51g; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - reading: T(supⱼ uⱼ) for uⱼ ∈ M(S), T an operator on M(S) → uⱼ bounded Borel with a common upper bound C; reason: this is exactly the condition supⱼ uⱼ ∈ M(S) (bounded below by u₀, measurable as a countable supremum), which the paper needs for T(supⱼ uⱼ) to be defined
--   - encoding: (d), increasing case: Tuⱼ ↑ Tu on {supⱼ Tuⱼ > −∞} → at every state; reason: in cases D and P every Tuⱼ is real, so the set is all of S
--   - encoding: stages numbered from 1, β^{j−1} weights → stages numbered from 0, weight P.β ^ j; reason: index shift only; Lean stage j is the paper's stage j + 1
--   - encoding: positive bounded return I(π) in [0, R] → Pos.I = real value of the [0, ∞] sum Pos.Data.IE, bounded by R in the problem; reason: the bound makes the real value exact; no instance changes
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 879, Theorem 5.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_Stationary_Model
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)
open NegativeDP.Stationary (switchAt prefixPlan IsSemiMarkov IsMarkov IsRandomSemiMarkov IsRandomMarkov)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 5.1 (p. 879), discounted case (first conjunct) and positive bounded case (second
conjunct), on `M(S)` = bounded Borel functions:
(a) `T` is monotone; (b) `T(u + c) = Tu + βc`; (c) `T(supⱼ uⱼ) ≥ supⱼ Tuⱼ` (for `supⱼ uⱼ ∈ M(S)`);
(d) `uⱼ ↓ u` implies `Tuⱼ ↓ Tu`, and `uⱼ ↑ u` implies `Tuⱼ ↑ Tu`;
(e) D: `‖Tu − Tv‖ ≤ β‖u − v‖`; P: `u ≥ 0` implies `Tu ≥ 0`;
(f) `TI(π) = I(f, π)` for every policy `π`, and `TI(f^(∞)) = I(f^(∞)) = lim Tⁿ0`;
(g) for a Markov `π = {f₁, f₂, …}`, `Iₙ(π, v) = T₁ ⋯ Tₙ v` (right fold over the rules
`m 0, …, m (n - 1)`). The negative case is the published `NegativeDP.Stationary.theorem51a`,
`theorem51bce`, `theorem51d`, `theorem51f` and `theorem51g`. -/
theorem theorem51 :
    (∀ (P : Problem S A) (f : {g : S → A // Measurable g}),
      (∀ u v : S → ℝ, IsBM u → IsBM v → (∀ s, u s ≤ v s) → ∀ s, T P f u s ≤ T P f v s) ∧
      (∀ (u : S → ℝ) (c : ℝ), IsBM u → ∀ s, T P f (fun t => u t + c) s = T P f u s + P.β * c) ∧
      (∀ uj : ℕ → S → ℝ, (∀ j, IsBM (uj j)) → (∃ C : ℝ, ∀ j s, uj j s ≤ C) →
        ∀ s, (⨆ j, T P f (uj j) s) ≤ T P f (fun t => ⨆ j, uj j t) s) ∧
      (∀ (uj : ℕ → S → ℝ) (u : S → ℝ), (∀ j, IsBM (uj j)) → IsBM u →
        ((Antitone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          ∀ s, Antitone (fun j => T P f (uj j) s) ∧
            Tendsto (fun j => T P f (uj j) s) atTop (𝓝 (T P f u s))) ∧
        ((Monotone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          ∀ s, Monotone (fun j => T P f (uj j) s) ∧
            Tendsto (fun j => T P f (uj j) s) atTop (𝓝 (T P f u s)))) ∧
      (∀ u v : S → ℝ, IsBM u → IsBM v →
        supNorm (fun s => T P f u s - T P f v s) ≤ P.β * supNorm (fun s => u s - v s)) ∧
      ((∀ π : Plan (S := S) (A := A), ∀ s, T P f (I P π) s = I P (prefixPlan f π) s) ∧
        (∀ s, T P f (I P (stationary f).toPlan) s = I P (stationary f).toPlan s) ∧
        ∀ s, Tendsto (fun n => (T P f)^[n] 0 s) atTop (𝓝 (I P (stationary f).toPlan s))) ∧
      (∀ (m : MarkovPlan S A) (n : ℕ) (v : S → ℝ), IsBM v →
        ∀ s, Disc.In P m.toPlan n v s = (List.range n).foldr (fun k w => T P (m k) w) v s)) ∧
    (∀ (P : Pos.Problem S A) (f : {g : S → A // Measurable g}),
      (∀ u v : S → ℝ, IsBM u → IsBM v → (∀ s, u s ≤ v s) → ∀ s, Pos.T P f u s ≤ Pos.T P f v s) ∧
      (∀ (u : S → ℝ) (c : ℝ), IsBM u → ∀ s, Pos.T P f (fun t => u t + c) s = Pos.T P f u s + c) ∧
      (∀ uj : ℕ → S → ℝ, (∀ j, IsBM (uj j)) → (∃ C : ℝ, ∀ j s, uj j s ≤ C) →
        ∀ s, (⨆ j, Pos.T P f (uj j) s) ≤ Pos.T P f (fun t => ⨆ j, uj j t) s) ∧
      (∀ (uj : ℕ → S → ℝ) (u : S → ℝ), (∀ j, IsBM (uj j)) → IsBM u →
        ((Antitone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          ∀ s, Antitone (fun j => Pos.T P f (uj j) s) ∧
            Tendsto (fun j => Pos.T P f (uj j) s) atTop (𝓝 (Pos.T P f u s))) ∧
        ((Monotone uj ∧ ∀ s, Tendsto (fun j => uj j s) atTop (𝓝 (u s))) →
          ∀ s, Monotone (fun j => Pos.T P f (uj j) s) ∧
            Tendsto (fun j => Pos.T P f (uj j) s) atTop (𝓝 (Pos.T P f u s)))) ∧
      (∀ u : S → ℝ, IsBM u → (∀ s, 0 ≤ u s) → ∀ s, 0 ≤ Pos.T P f u s) ∧
      ((∀ π : Plan (S := S) (A := A), ∀ s, Pos.T P f (Pos.I P π) s = Pos.I P (prefixPlan f π) s) ∧
        (∀ s, Pos.T P f (Pos.I P (stationary f).toPlan) s = Pos.I P (stationary f).toPlan s) ∧
        ∀ s, Tendsto (fun n => (Pos.T P f)^[n] 0 s) atTop (𝓝 (Pos.I P (stationary f).toPlan s))) ∧
      (∀ (m : MarkovPlan S A) (n : ℕ) (v : S → ℝ), IsBM v →
        ∀ s, Pos.In P m.toPlan n v s = (List.range n).foldr (fun k w => Pos.T P (m k) w) v s)) := by sorry

end NegativeDP.EssFinite.Supplement
