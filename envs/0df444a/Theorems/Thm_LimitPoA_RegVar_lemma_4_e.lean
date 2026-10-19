-- Prove2me | Theorems.Thm_LimitPoA_RegVar_lemma_4_e
-- name    : LimitPoA.RegVar.lemma_4_e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:50.633332+00:00
-- url     : https://prove2.me/theorems/04cb8e3a-76c4-4e67-84a8-9e2475a9a68b
-- title:
--   Lemma 4 e), p. 15 — along a scalable sequence the scaled NE cost tends to the limit NE cost in (0, ∞) and PoA(d⁽ⁿ⁾) → 1
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, with cost functions in the class of §2.1 that are not identically zero on $(0,\infty)$. Let $(d^{(n)})_{n\in\mathbb N}$ be a regular sequence with limit distribution $d^{(\infty)}$, let $(g_n)$ be a scaling sequence, and suppose that $\Gamma^{(\infty)} = \lim_{d^{(n)}\to\infty}\Gamma^{[g_n]}$ is a limit game (Definition 3.2). Let $\tilde f^{(n)}$ be an NE profile of $\Gamma$ for $d^{(n)}$, for each $n$, and let $\tilde f^{(\infty)}$ be an NE profile of $\Gamma^{(\infty)}$ w.r.t. $d^{(\infty)}$. Then
--   $$\lim_{n\to\infty}\frac{C(\tilde f^{(n)})}{T(d^{(n)})\cdot g_n} = C_{\Gamma^{(\infty)}}(\tilde f^{(\infty)}) \in (0,\infty)$$
--   and
--   $$\lim_{n\to\infty}\mathrm{PoA}(d^{(n)}) = \mathrm{PoA}(d^{(\infty)}) = 1.$$
--
--   This is the scaling theorem behind Theorem 3.1: along a scalable sequence the price of anarchy tends to 1.
--
--   **Formalization Note** The limit cost $C_{\Gamma^{(\infty)}}$ lies in $[0,\infty]$; the statement asserts it is positive and finite and that the real ratios converge to its real value. $\mathrm{PoA}(d^{(\infty)}) = 1$ is part of the hypothesis (L4); the conclusion keeps $\lim_n \mathrm{PoA}(d^{(n)}) = 1$, stated independently of the choice of $\tilde f^{(\infty)}$.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 15, Lemma 4 e) (proof Appendix A.1, pp. 34–38)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit

namespace LimitPoA.RegVar

open Filter Topology ENNReal

/-- Lemma 4 e), p. 15: if `Γ^(∞) = lim_{d^(n)→∞} Γ^[g_n]`, then `C(f̃^(n))/(T(d^(n))·g_n)` tends to the
cost `C_{Γ^(∞)}(f̃^(∞)) ∈ (0, ∞)` of any NE profile `f̃^(∞)` of `Γ^(∞)`, and `PoA(d^(n)) → 1`. -/
theorem lemma_4_e (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (d : ℕ → Fin Γ.Sd → ℝ) (g : ℕ → ℝ) (dInf : Fin Γ.Sd → ℝ) (τInf : Fin Γ.J → ℝ → ℝ≥0∞)
    (hlim : IsLimitGame Γ τ Finset.univ d g dInf τInf) :
    (∀ fNE : ℕ → Fin Γ.R → ℝ, (∀ n, IsNE Γ τ (d n) (fNE n)) →
      ∀ fInf : Fin Γ.R → ℝ, IsLimNE Γ τInf dInf fInf →
        Tendsto (fun n => cost Γ τ (fNE n) / (totalDemand Γ (d n) * g n)) atTop
            (𝓝 (limCost Γ τInf fInf).toReal) ∧
          0 < limCost Γ τInf fInf ∧ limCost Γ τInf fInf < ⊤) ∧
    Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1) := by sorry

end LimitPoA.RegVar
