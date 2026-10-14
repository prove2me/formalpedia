-- Prove2me | Theorems.Thm_LambdaVaRAmb_Comono_theorem_4
-- name    : LambdaVaRAmb.Comono.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:50.101477+00:00
-- url     : https://prove2.me/theorems/bd980eca-d771-4177-8c2a-4aa2938c7d21
-- title:
--   Theorem 4 — comonotonic sharing of nonnegative ΛᵢVaR^{wᵢ}: ⊞ = min, all risk to one agent; for all X iff Λ is constant on (−∞,0)
-- statement:
--   Let $n\ge1$ agents share a risk $X$ from an admissible set $\mathcal X$ of random variables. Agent $i$ evaluates risk by $\Lambda_i\mathrm{VaR}^{w_i}$, where $\Lambda_i\in\mathcal H_I$ (increasing, with values in $(0,1)$) and $w_i$ is a continuous capacity. Allocations are restricted to $\mathbb A_n^+(X)$, the comonotonic allocations whose components have the same sign, and $\boxplus$ denotes the infimum of the total risk over them.
--
--   1. If $\Lambda_i\mathrm{VaR}^{w_i}(X)\ge0$ for every $i$, then
--   $$\boxplus_{i=1}^n\Lambda_i\mathrm{VaR}^{w_i}(X)=\min_{i\in[n]}\Lambda_i\mathrm{VaR}^{w_i}(X),\tag{11}$$
--   and for every $i_0\in\arg\min_{i\in[n]}\Lambda_i\mathrm{VaR}^{w_i}(X)$ the allocation $X_{i_0}=X$, $X_i=0$ for $i\ne i_0$, is an optimal allocation: it lies in $\mathbb A_n^+(X)$ and attains the infimum.
--   2. If every $\Lambda_i$ is constant on $(-\infty,0)$, then (11) holds for all $X\in\mathcal X$.
--   3. If $n\ge2$, $w_1=\dots=w_n$, $w_1$ is atomless and $\Lambda_1=\dots=\Lambda_n$, then (11) holds for all $X\in\mathcal X$ if and only if $\Lambda_1$ is constant on $(-\infty,0)$.
--
--   The theorem says that under comonotonic risk sharing the optimal arrangement is to give the whole risk to the agent with the smallest ΛVaR, and that this extends to risks of any sign exactly when the level functions are flat on the negative half-line.
--
--   **Formalization Note** ΛVaR, sums and the minimum are in $[-\infty,\infty]$ (`EReal`); the minimum over $[n]$ is `⨅ i : Fin n`, nonempty since $n\ge1$. "One optimal allocation is of the form …" is stated for every minimising index $i_0$, as membership in $\mathbb A_n^+(X)$ together with attainment of $\boxplus$. Disclosed additions: $n\ge1$ (the paper's "$n$ agents"; for $n=0$ the identity fails); $n\ge2$ in part 3 (for $n=1$, (11) holds for every $X$ and every $\Lambda$, so "necessary" fails, and the paper's proof uses a second agent); the weak same-sign reading of $\mathbb A_n^+$ (see the definition file); "$w_1=\dots=w_n$" is equality on measurable sets. "Constant on $(-\infty,0)$" says nothing about the value at $0$. "For all $X\in\mathcal X$" ranges over the admissible set $\mathcal X$ itself, whose closure properties are fixed in the definition file.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 21, Theorem 4 (display (11))

import Mathlib
import Definitions.Def_LambdaVaRAmb_Comono_Setting

namespace LambdaVaRAmb.Comono

/-- Theorem 4, p. 21: comonotonic risk sharing of `ΛᵢVaR^{wᵢ}` under continuous capacities. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : LambdaVaRAmb.InfConv.IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InHI (Λ i)) (hw : ∀ i, LambdaVaRAmb.InfConv.IsContinuousCapacity (w i)) :
    (∀ X ∈ dom, (∀ i, 0 ≤ LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) →
      comonoInfConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X ∧
      ∀ i₀ : Fin n, LambdaVaRAmb.Robust.LVaR (Λ i₀) (w i₀) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X →
        IsComonoOptimal dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X
          (fun i => if i = i₀ then X else fun _ => 0)) ∧
    ((∀ i, ∀ x y, x < 0 → y < 0 → Λ i x = Λ i y) →
      ∀ X ∈ dom, comonoInfConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ∧
    (2 ≤ n → (∀ i, ∀ A, MeasurableSet A → w i A = w ⟨0, hn⟩ A) →
      IsAtomlessCapacity (w ⟨0, hn⟩) → (∀ i, Λ i = Λ ⟨0, hn⟩) →
      ((∀ X ∈ dom, comonoInfConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ↔
        ∀ x y, x < 0 → y < 0 → Λ ⟨0, hn⟩ x = Λ ⟨0, hn⟩ y)) := by sorry

end LambdaVaRAmb.Comono
