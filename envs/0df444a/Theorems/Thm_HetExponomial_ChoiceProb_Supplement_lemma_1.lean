-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_lemma_1
-- name    : HetExponomial.ChoiceProb.Supplement.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:40:57.578197+00:00
-- url     : https://prove2.me/theorems/95dd51ae-c8a4-4eb1-a8ff-3a2554e96f57
-- title:
--   Lemma 1, pp. 27–28 — properties (a)–(d) of τ_i = Q_i/(∂Q_i/∂u_i)
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the $n$-firm oligopoly, firm $i$ sells product $i$, chooses a price $p_i\ge 0$ (equivalently $u_i\le\alpha_i$) and earns $R_i=p_i\,Q_i$. A **Nash equilibrium in prices** is a price vector $p^*\ge 0$ from which no firm can raise its revenue by changing its own price to any other nonnegative price; $u^*_i=\alpha_i-\beta p^*_i$, $Q^*_i$ and $R^*_i$ are the equilibrium ideal utilities, market shares and revenues. The ratio $\tau_i(\mathbf u)=Q_i(\mathbf u)/(\partial Q_i(\mathbf u)/\partial u_i)$ is (12), $L=\sum_{k\in N}\lambda_k$, $M=\max_{j}\alpha_j$, and for a set $S$ of solved products with values $u^*_k$, $\tau_i(u_i\mid u(S))$ is $\tau_i$ evaluated with coordinate $i$ equal to $u_i$, coordinate $k\in S$ equal to $u^*_k$, and every other coordinate equal to $M$ (13). Let $\zeta_i=\min_{j\ne i}u_j$. For every $i\in N$ and every $\alpha_i\in\mathbb R$:
--
--   1. **(a) Monotonicity and positivity.** $\tau_i(\mathbf u)>0$ for every $\mathbf u$, and $\tau_i$ is continuous on $\mathbb R^n$. As a function of $u_i$ (the other coordinates fixed), $\tau_i$ equals its minimum value $1/(L-\lambda_i)$ on $(-\infty,\zeta_i]$, is never below that value, and is strictly increasing on $(\zeta_i,\alpha_i]$.
--   2. **(b) First-order condition.** As a function of $u_i$, $\tau_i$ crosses $\alpha_i-u_i$ exactly once: the equation $\alpha_i-u_i=\tau_i(\mathbf u)$ has exactly one real solution $u_i$, and exactly one on $(-\infty,\alpha_i]$.
--   3. **(c) Independence from higher ideal utilities.** $\tau_i(\mathbf u)$ does not depend on the coordinates $u_j$, $j\ne i$, with $u_j\ge u_i$: if $\mathbf v$ agrees with $\mathbf u$ in coordinate $i$ and in every coordinate $j$ with $u_j<u_i$, and $v_j\ge u_i$ whenever $j\ne i$ and $u_j\ge u_i$, then $\tau_i(\mathbf v)=\tau_i(\mathbf u)$.
--   4. **(d) Crossover points.** For distinct $i,j$ with $u_i=u_j$,
--   $$
--   \tau_i(\mathbf u)\le\tau_j(\mathbf u)\iff\lambda_i\le\lambda_j,\qquad \tau_i(\mathbf u)<\tau_j(\mathbf u)\iff\lambda_i<\lambda_j .
--   $$
--
--   The first-order conditions of the price game are $\alpha_i-u_i=\tau_i(\mathbf u)$ (12). Parts (a)–(c) let each firm's condition be solved for its own ideal utility knowing only the lower ideal utilities, which is the basis of the algorithms of Theorems 10–13.
--
--   **Formalization Note** $\tau_i$ divides $Q_i$ by the actual partial derivative `partialU` of $Q_i$ in $u_i$. "$u_i\in(-\infty,\zeta_i]$" is written as $u_i\le u_j$ for every $j\ne i$, and "$u_i>\zeta_i$" as $u_j<u_i$ for some $j\ne i$. $\alpha_i$ enters only as the right end of the interval in (a) and the right side of the equation in (b); the lemma is stated for every real $\alpha_i$.
--
--   Differences from the source:
--   - encoding: ζ_i = min_{j∈N, j≠i} u_j and the intervals (−∞, ζ_i], (ζ_i, α_i] → x ≤ u j for all j ≠ i, and (∃ j ≠ i, u j < x) ∧ x ≤ α i; reason: the same sets for n ≥ 2, without a junk-valued minimum
--   - encoding: "as a function of u_i" with α_i the firm's parameter → t ↦ τ_i(u with u_i := t), for every u and every real α_i; reason: the lemma concerns τ_i on ℝ^n with α_i fixed but arbitrary
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), pp. 27–28, Lemma 1; (12), p. 27; proof pp. 58–61

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem lemma_1 {n : ℕ} (hn : 2 ≤ n) (α lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) :
    -- (a) Monotonicity and Positivity
    ((∀ u, 0 < tau u lam i) ∧ Continuous (fun u => tau u lam i) ∧
      (∀ (u : Fin n → ℝ) (x : ℝ), (∀ j, j ≠ i → x ≤ u j) →
          tau (Function.update u i x) lam i = 1 / (Ltot lam - lam i)) ∧
      (∀ (u : Fin n → ℝ) (x : ℝ), 1 / (Ltot lam - lam i) ≤ tau (Function.update u i x) lam i) ∧
      (∀ u : Fin n → ℝ, StrictMonoOn (fun x => tau (Function.update u i x) lam i)
          {x | (∃ j, j ≠ i ∧ u j < x) ∧ x ≤ α i})) ∧
    -- (b) First-order Condition
    (∀ u : Fin n → ℝ,
      (∃! x : ℝ, α i - x = tau (Function.update u i x) lam i) ∧
        ∃! x : ℝ, x ≤ α i ∧ α i - x = tau (Function.update u i x) lam i) ∧
    -- (c) Independence from Higher Ideal Utilities
    (∀ u v : Fin n → ℝ, v i = u i → (∀ j, u j < u i → v j = u j) →
      (∀ j, j ≠ i → u i ≤ u j → u i ≤ v j) → tau v lam i = tau u lam i) ∧
    -- (d) Crossover Points
    (∀ (u : Fin n → ℝ) (j : Fin n), j ≠ i → u i = u j →
      (tau u lam i ≤ tau u lam j ↔ lam i ≤ lam j) ∧
        (tau u lam i < tau u lam j ↔ lam i < lam j)) := by sorry

end HetExponomial.ChoiceProb.Supplement
