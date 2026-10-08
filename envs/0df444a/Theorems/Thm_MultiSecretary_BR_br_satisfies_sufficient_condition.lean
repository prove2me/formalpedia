-- Prove2me | Theorems.Thm_MultiSecretary_BR_br_satisfies_sufficient_condition
-- name    : MultiSecretary.BR.br_satisfies_sufficient_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:18:58.337992+00:00
-- url     : https://prove2.me/theorems/7fde2f64-b2a4-4920-9791-e292f235ed46
-- title:
--   Corollary 1 — the BR policy and $\tau$ of (20) satisfy conditions (i)–(iv) of Proposition 2
-- statement:
--   Let $\epsilon>0$ and $0<\delta<\epsilon$. There is a constant $M$ such that for every multi-secretary instance with $\tfrac12\min\{f_m,\dots,f_1\}=\epsilon$ and every $(n,k)\in\mathcal T$, with $j_0=j_0(n,k)$:
--
--   1. the Budget-Ratio policy is a feasible online policy, $\mathrm{br}\in\Pi(n,k)$;
--   2. the time $\tau$ of (20) is a stopping time with $\tau\le n$;
--   3. $\sum_{j\in[j_0-1]}\mathbb E[S^{\mathrm{br},\tau}_j]=\sum_{j\in[j_0-1]}\mathbb E[Z^\tau_j]$;
--   4. $\mathbb E[S^{\mathrm{br},\tau}_{j_0}]\ge\mathbb E[\mathfrak S^\tau_{j_0}]-M$;
--   5. $\mathbb E[S^{\mathrm{br},\tau}_{j_0+1}]\ge\mathbb E[\mathfrak S^\tau_{j_0+1}]-M$ (when $j_0<m$);
--   6. $\mathbb E[\tau]\ge n-M$.
--
--   With Proposition 2 this gives $V^*_{\mathrm{off}}-V^{\mathrm{br}}_{\mathrm{on}}\le3a_1M+a_1/(4\epsilon)$ uniformly, the goal of the mission.
--
--   **Formalization Note** This formalizes the first sentence of Corollary 1; the "in particular" bound is the mission's goal. As in Theorem 2, $M$ depends on $\delta$ as well as on $\epsilon$ (the page writes $M\equiv M(\epsilon)$), and is chosen before the instance, $n$ and $k$. Condition 5 is omitted for $j_0=m$, as in Proposition 2. Lean index $i$ of `Fin m` is the paper's index $i+1$, so `a 0` is $a_1$, the largest ability.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Corollary 1, p. 16; proof pp. 17–19

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model
import Definitions.Def_MultiSecretary_BR_Policy

namespace MultiSecretary.BR

open Finset

/-- Corollary 1 (Uniformly bounded regret), p. 16, first sentence: the BR policy and the stopping
time `τ` of (20) satisfy the properties in Proposition 2. Precisely: for `ϵ = ½ min_j f_j` and
`0 < δ < ϵ` there is a constant `M` such that for every instance with this `ϵ` and all
`(n, k) ∈ T`, `br ∈ Π(n, k)`, `τ ≤ n` is a stopping time, and (i)–(iv) of Proposition 2 hold with
`j₀ = j₀(n, k)` and this `M`. (`M` depends on `δ` as well as on `ϵ`, as in Theorem 2.) -/
theorem br_satisfies_sufficient_condition (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ < ε) :
    ∃ M : ℝ, ∀ (m : ℕ) (I : Instance m), I.eps = ε → ∀ n k : ℕ, k ≤ n →
      I.brPolicy n k ∈ policies n m k ∧
      (∀ x, I.tau δ n k x ≤ n) ∧
      (∀ x y : Fin n → Fin m, (∀ s : Fin n, s.val < I.tau δ n k x → x s = y s) →
        I.tau δ n k y = I.tau δ n k x) ∧
      (∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
          I.E (fun x => (onCount (I.brPolicy n k) (I.tau δ n k x) j x : ℝ)) =
        ∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
          I.E (fun x => (Z (I.tau δ n k x) j x : ℝ))) ∧
      (I.E (fun x => (offCount k (I.tau δ n k x) (I.actionIndex n k) x : ℝ)) - M ≤
        I.E (fun x => (onCount (I.brPolicy n k) (I.tau δ n k x) (I.actionIndex n k) x : ℝ))) ∧
      (∀ h : (I.actionIndex n k).val + 1 < m,
        I.E (fun x => (offCount k (I.tau δ n k x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ)) - M ≤
        I.E (fun x =>
          (onCount (I.brPolicy n k) (I.tau δ n k x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ))) ∧
      ((n : ℝ) - M ≤ I.E (fun x : Fin n → Fin m => (I.tau δ n k x : ℝ))) := by sorry

end MultiSecretary.BR
