-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_5
-- name    : HLambdaG.Main.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:05:24.433584+00:00
-- url     : https://prove2.me/theorems/fdd00f04-e902-4208-ad28-061d459c21e0
-- title:
--   Theorem 5, p. 641 — sample-path L = λW converse: from t⁻¹S₁(t) → λ and H(t) → L, bounds and limits for n⁻¹Σ_{k≤n} W_k
-- statement:
--   Consider the $L=\lambda W$ framework of §1.2. Arrival epochs satisfy $0=T_0\le T_n\le T_{n+1}$ and $T_n\to\infty$, and departure epochs satisfy $D_n\ge T_n$. Waiting times are $W_n=D_n-T_n$. The time average is $H(t)=t^{-1}\sum_{k\ge1}F_k(t)$ with $F_k$ of (7), the time-average number in system. The queue length is $Q(t)=\#\{k\ge1:T_k\le t\le D_k\}$, and $S_1(t)=\inf\{s\ge0:T_{[s]}>t\}$ is the inverse (3) of $T_1(s)=T_{[s]}$. Suppose that, for some $0<\lambda<\infty$ and finite $L$,
--   $$
--   t^{-1}S_1(t)\to\lambda\quad\text{and}\quad H(t)\to L\qquad(t\to\infty).
--   $$
--   Then:
--
--   1. (a) $\displaystyle\liminf_{n\to\infty}n^{-1}\sum_{k=1}^nW_k\ge\lambda^{-1}L$;
--   2. (b) if, in addition, there is an increasing sequence $t_k\to\infty$ with $Q(t_k)=0$ for all $k$, then $\displaystyle\liminf_{n\to\infty}n^{-1}\sum_{k=1}^nW_k=\lambda^{-1}L$;
--   3. (c) if, in addition to the assumptions of (a), $n^{-1}W_n\to0$, then $\displaystyle\lim_{n\to\infty}n^{-1}\sum_{k=1}^nW_k=\lambda^{-1}L$.
--
--   This is the converse direction of the sample-path $L=\lambda W$: the arrival rate and the time-average queue length determine the customer-average waiting time, under the mild extra conditions (b) or (c). Remark 6 shows that (b) cannot be strengthened to convergence.
--
--   **Formalization Note** The lim inf is taken in the extended reals, since $n^{-1}\sum_{k\le n}W_k$ may be unbounded. $H$ is the published marginal average of the §1.1 input built from (7), and $S_1$ is the published inverse `inv` of the step time change. "Increasing" is read as strictly increasing; together with $t_k\to\infty$, a nondecreasing sequence would give the same statement. Part (b) is stated as an implication for every such sequence.
--
--   Differences from the source:
--
--   - encoding: lim inf / lim sup, possibly infinite → Filter.liminf / Filter.limsup of the EReal coercion (published liminfE / limsupE), with λ multiplied inside the real function; reason: Lean convention; a real lim inf/lim sup of an unbounded function would be a junk value, and EReal keeps the page's possibly infinite values
--   - encoding: s, t ∈ [0, ∞), customers k = 1, 2, … → s, t : ℝ≥0; customers indexed by ℕ with a dummy index 0 (F_0 = 0); reason: Lean convention; the index 0 carries no customer and every sum starts at k = 1, so no instance changes
--   - encoding: an increasing unbounded sequence of empty-system epochs → a StrictMono unbounded sequence indexed from zero; reason: an unbounded nondecreasing sequence has a strictly increasing subsequence; the conclusion is independent of the chosen sequence, so the existence hypotheses are equivalent
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 641, Theorem 5 (a)–(c); setting §1.2 p. 636 and Q(t) p. 640; https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_LittleLaw

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 5, p. 641: in the `L = λW` framework of §1.2, if `t⁻¹S₁(t) → λ ∈ (0, ∞)` and
`H(t) → L`, then (a) `lim inf n⁻¹ Σ_{k ≤ n} W_k ≥ λ⁻¹L`; (b) if moreover `Q(t_k) = 0` along an
increasing sequence `t_k → ∞`, the lim inf equals `λ⁻¹L`; (c) if moreover `n⁻¹W_n → 0`,
then `n⁻¹ Σ_{k ≤ n} W_k → λ⁻¹L`. -/
theorem theorem_5 (L : LWSetting) (lam Lval : ℝ) (hlam : 0 < lam)
    (hS₁ : Tendsto (fun t : ℝ≥0 => (inv L.toDiscrete.T1 t : ℝ) / (t : ℝ)) atTop (𝓝 lam))
    (hH : Tendsto (H L.toDiscrete.input) atTop (𝓝 Lval)) :
    ((lam⁻¹ * Lval : ℝ) : EReal) ≤ Filter.liminf (fun n : ℕ =>
        ((((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.W k : ℝ) : EReal)) atTop ∧
    (∀ t : ℕ → ℝ≥0, StrictMono t → Tendsto t atTop atTop → (∀ k, L.Q (t k) = 0) →
      Filter.liminf (fun n : ℕ =>
        ((((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.W k : ℝ) : EReal)) atTop =
          ((lam⁻¹ * Lval : ℝ) : EReal)) ∧
    (Tendsto (fun n : ℕ => L.W n / (n : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 n, L.W k) atTop
        (𝓝 (lam⁻¹ * Lval))) := by sorry

end HLambdaG.Main.Supplement
