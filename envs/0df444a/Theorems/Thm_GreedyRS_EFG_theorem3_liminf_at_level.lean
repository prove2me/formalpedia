-- Prove2me | Theorems.Thm_GreedyRS_EFG_theorem3_liminf_at_level
-- name    : GreedyRS.EFG.theorem3_liminf_at_level
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T10:35:48.09032+00:00
-- url     : https://prove2.me/theorems/8eb43d89-8926-4c42-80da-af761b288df9
-- title:
--   Proof of Theorem 3, p. ec6 — liminf PCS ≥ Pr{min_{n≥n₀} X̄₁(n) > μ₁ − γ'} whenever C((γ−γ')/σ̄; n₀) < n₀ + n_g
-- statement:
--   This is the core estimate in the proof of Theorem 3 (sample optimality of the explore-first greedy (EFG) procedure): the EFG analogue of the corresponding bound in the proof of Theorem 1, combined with Lemma 3.
--
--   Consider $k$ alternatives with independent normal observations $X_{ij}\sim N(\mu_i,\sigma_i^2)$, $\sigma_i^2>0$, alternative 1 the best, and suppose **Assumption 1** holds: $\mu_1-\mu_i\ge\gamma>0$ for all $i\ge2$ and $\sigma_i^2\le\bar\sigma^2$ for all $i$, regardless of $k$. Let $C(x;n_0)=\mathrm E[\tilde N(x;n_0)]$, where $\tilde N(x;n_0)=\inf\{n\ge n_0:\bar Z(n)<x\}$ for an iid $N(0,1)$ sequence. Fix $n_0\ge1$, $n_g\in\mathbb R$, and a level $\gamma_\epsilon^-\in(0,\gamma)$ with
--
--   $$C\Big(\frac{\gamma-\gamma_\epsilon^-}{\bar\sigma};n_0\Big)<n_0+n_g .$$
--
--   Then the EFG procedure with exploration size $n_0$ and total budget $B=\lfloor(n_0+n_g)k\rfloor$ satisfies
--
--   $$\liminf_{k\to\infty}\mathrm{PCS}\ \ge\ \Pr\Big\{\min_{n\ge n_0}\bar X_1(n)>\mu_1-\gamma_\epsilon^-\Big\}.$$
--
--   In the paper this is the display preceding "Letting $\epsilon\to0$" in the proof of Theorem 3, where $\gamma_\epsilon^-$ is chosen with $C((\gamma-\gamma_\epsilon^-)/\bar\sigma;n_0)=c-2\epsilon<c=n_0+n_g$, and where the term $\Pr\{\arg\min_{n\ge n_0}\bar X_1(n)=\infty\}$ has already been removed using Lemma 3. Theorem 3 follows from it by letting $\gamma_\epsilon^-\uparrow\gamma_0$.
--
--   **Formalization Note** Only the strict inequality $C((\gamma-\gamma_\epsilon^-)/\bar\sigma;n_0)<n_0+n_g$ (in $[0,\infty]$) is assumed, which is all the proof uses. "$\min_{n\ge n_0}\bar X_1(n)>a$" means the path is bounded below from $n_0$ on and its infimum exceeds $a$. Alternatives are indexed from $0$ (Lean's $0$ is the paper's alternative 1); one observation array serves all $k$; the budget is $\lfloor(n_0+n_g)k\rfloor$. Probabilities and the liminf live in $[0,\infty]$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, E-companion, Proof of Theorem 3 (p. ec6), Eqs. (proof: PCS_EFG1)–(proof: PCS_EFG3), following the proof of Theorem 1 (Eqs. thm1: C1 – thm1: PCS4) and Lemma 3; Assumption 1, p. 12

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem theorem3_liminf_at_level {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (n0 : ℕ) (hn0 : 1 ≤ n0) (ng : ℝ) (γ1 : ℝ) (hγ1 : γ1 ∈ Set.Ioo 0 γ)
    (hC : GreedyRS.Greedy.Cn0 ((γ - γ1) / σbar) n0 < ENNReal.ofReal (n0 + ng)) :
    P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ1)} ≤
      Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) Filter.atTop := by sorry

end GreedyRS.EFG
