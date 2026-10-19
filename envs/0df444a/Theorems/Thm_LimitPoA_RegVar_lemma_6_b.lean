-- Prove2me | Theorems.Thm_LimitPoA_RegVar_lemma_6_b
-- name    : LimitPoA.RegVar.lemma_6_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:18.589878+00:00
-- url     : https://prove2.me/theorems/a5ad8c29-aa90-43cf-a378-10dc22df8828
-- title:
--   Lemma 6 b), p. 20 — inequality chain (3.2) and limsup PoA(d⁽ⁿ⁾) ≤ limsup PoA‾(d⁽ⁿ⁾)
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, with cost functions in the class of §2.1 that are not identically zero on $(0,\infty)$, and let $(d^{(n)})$ be a decomposable sequence with an asymptotic decomposition $\Gamma \asymp_{d^{(n)}} \Gamma_{|\mathcal K_1}\oplus\cdots\oplus\Gamma_{|\mathcal K_m}$, $\mathcal M = \{1,\dots,m\}$. Then:
--
--   1. for every $n$, every $u \in \mathcal M$, every SO profile $f^{*(n)}$ of $\Gamma$ for $d^{(n)}$ and every SO profile $f^{*(\mathcal K_u,n)}$ of $\Gamma_{|\mathcal K_u}$ for $d^{(n)}_{|\mathcal K_u}$,
--   $$\sum_{k\in\mathcal K_u}\sum_{s\in\mathcal S_k} f^{*(n)}_s\,\tau_s(f^{*(n)}) \;\ge\; C_{\Gamma_{|\mathcal K_u}}(f^{*(n)}_{|\mathcal K_u}) \;\ge\; C_{\Gamma_{|\mathcal K_u}}(f^{*(\mathcal K_u,n)}); \qquad (3.2)$$
--   2. for any sequence of SO profiles $f^{*(n)}$, the limsup of $\mathrm{PoA}(d^{(n)})$ equals that of the NE cost divided by $\sum_u$ of the joint contributions of the classes to $C(f^{*(n)})$; and consequently
--   $$\limsup_{n\to\infty}\mathrm{PoA}(d^{(n)}) \le \limsup_{n\to\infty}\frac{C(\tilde f^{(n)})}{\sum_{u\in\mathcal M} C_{\Gamma_{|\mathcal K_u}}(f^{*(\mathcal K_u,n)})} = \limsup_{n\to\infty}\overline{\mathrm{PoA}}(d^{(n)}), \qquad \overline{\mathrm{PoA}}(d^{(n)}) = \frac{C(\tilde f^{(n)})}{\sum_{u\in\mathcal M} C_{\Gamma_{|\mathcal K_u}}(\tilde f^{(\mathcal K_u,n)})}.$$
--
--   The bound $\overline{\mathrm{PoA}}$ removes SO profiles of $\Gamma$ from the convergence analysis.
--
--   **Formalization Note** The page writes "for each $u \in \mathcal K_u$"; this is a slip for $u \in \mathcal M$. The middle term is the cost of the restricted profile $f^{*(n)}_{|\mathcal K_u}$, whose loads are the independent consumptions $\sum_{k\in\mathcal K_u}\sum_{s\in\mathcal S_k: a\in s} f_s$ (the intended reading of p. 19, which prints $\sum_{k\in\mathcal K}$). The lim sups are taken of the real values coerced to `EReal`. The formal statement includes the two equalities printed between the initial PoA limsup and the final upper bound.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 20, Lemma 6 b) and (3.2); independent consumption p. 19

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp

namespace LimitPoA.RegVar

open Filter Topology

/-- Lemma 6 b), p. 20: (3.2) for every class, followed by the complete chain of
limsup equalities and inequalities ending at `\overline{PoA}`. Limsups are in `EReal`. -/
theorem lemma_6_b (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (d : ℕ → Fin Γ.Sd → ℝ) (hdec : IsDecomposable Γ Finset.univ d)
    (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) (g : Fin m → ℕ → ℝ)
    (hAD : IsAsymDecomp Γ τ Finset.univ d m cls g) :
    (∀ (n : ℕ) (u : Fin m) (fSO fSOu : Fin Γ.R → ℝ), IsSO Γ τ (d n) fSO →
        IsSO Γ τ (restrict Γ (cls u) (d n)) fSOu →
        cost Γ τ fSOu ≤ cost Γ τ (restrictProfile Γ (cls u) fSO) ∧
          cost Γ τ (restrictProfile Γ (cls u) fSO) ≤ jointTotalCost Γ τ (cls u) fSO) ∧
    (∀ fSO : ℕ → Fin Γ.R → ℝ, (∀ n, IsSO Γ τ (d n) (fSO n)) →
      limsup (fun n => ((PoA Γ τ (d n) : ℝ) : EReal)) atTop =
        limsup (fun n =>
          ((NECost Γ τ (d n) / ∑ u, jointTotalCost Γ τ (cls u) (fSO n) : ℝ) : EReal)) atTop) ∧
    limsup (fun n => ((PoA Γ τ (d n) : ℝ) : EReal)) atTop ≤
      limsup (fun n =>
        ((NECost Γ τ (d n) / ∑ u, SOCost Γ τ (restrict Γ (cls u) (d n)) : ℝ) : EReal)) atTop ∧
    limsup (fun n =>
        ((NECost Γ τ (d n) / ∑ u, SOCost Γ τ (restrict Γ (cls u) (d n)) : ℝ) : EReal)) atTop =
      limsup (fun n => ((PoABar Γ τ cls (d n) : ℝ) : EReal)) atTop := by sorry

end LimitPoA.RegVar
