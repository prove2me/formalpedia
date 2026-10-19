-- Prove2me | Theorems.Thm_LimitPoA_RegVar_lemma_6_a
-- name    : LimitPoA.RegVar.lemma_6_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:26.811738+00:00
-- url     : https://prove2.me/theorems/d1ef6cb1-d6a9-4f54-9a86-207bd749dd7b
-- title:
--   Lemma 6 a), p. 20 — in each class K_u of an asymptotic decomposition the subgame's NE/SO cost ratio → 1 and its scaled NE cost converges
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, with cost functions in the class of §2.1 that are not identically zero on $(0,\infty)$. Let $(d^{(n)})$ be a decomposable sequence with an asymptotic decomposition $\Gamma \asymp_{d^{(n)}} \Gamma_{|\mathcal K_1}\oplus\cdots\oplus\Gamma_{|\mathcal K_m}$ w.r.t. scaling sequences $(g^{(u)}_n)_n$, $u \in \mathcal M = \{1,\dots,m\}$. For each $u$ and $n$ let $\tilde f^{(\mathcal K_u,n)}$ and $f^{*(\mathcal K_u,n)}$ be an NE profile and an SO profile of the subgame $\Gamma_{|\mathcal K_u}$ w.r.t. $d^{(n)}_{|\mathcal K_u}$. Then, for each $u \in \mathcal M$,
--   $$\lim_{n\to\infty}\frac{C_{\Gamma_{|\mathcal K_u}}(\tilde f^{(\mathcal K_u,n)})}{C_{\Gamma_{|\mathcal K_u}}(f^{*(\mathcal K_u,n)})} = 1 \quad\text{and}\quad \lim_{n\to\infty}\frac{C_{\Gamma_{|\mathcal K_u}}(\tilde f^{(\mathcal K_u,n)})}{T(d^{(n)}_{|\mathcal K_u})\cdot g^{(u)}_n} = C_{\Gamma^{(\infty)}_{|\mathcal K_u}}(\tilde f^{(\mathcal K_u,\infty)}),$$
--   where $\Gamma^{(\infty)}_{|\mathcal K_u}$ is the limit of $\Gamma_{|\mathcal K_u}$ w.r.t. $(d^{(n)}_{|\mathcal K_u})_n$ under the scaling sequence $(g^{(u)}_n)_n$ and $\tilde f^{(\mathcal K_u,\infty)}$ is an NE profile of $\Gamma^{(\infty)}_{|\mathcal K_u}$.
--
--   **Formalization Note** Subgame profiles are profiles of $\Gamma$ for the zero-padded demand $d^{(n)}_{|\mathcal K_u}$. The second limit is stated for every limit game of the class $\mathcal K_u$ under $(g^{(u)}_n)$ and every NE profile of it.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 20, Lemma 6 a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp

namespace LimitPoA.RegVar

open Filter Topology ENNReal

/-- Lemma 6 a), p. 20: for every class `K_u` of an asymptotic decomposition, NE and SO costs of the
subgame `Γ|K_u` are asymptotically equal, and the scaled NE cost of `Γ|K_u` tends to the NE cost of
its limit game `Γ^(∞)_{|K_u}` under the scaling sequence `(g_n^(u))`. -/
theorem lemma_6_a (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (d : ℕ → Fin Γ.Sd → ℝ) (hdec : IsDecomposable Γ Finset.univ d)
    (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) (g : Fin m → ℕ → ℝ)
    (hAD : IsAsymDecomp Γ τ Finset.univ d m cls g)
    (fNE fSO : Fin m → ℕ → Fin Γ.R → ℝ)
    (hNE : ∀ u n, IsNE Γ τ (restrict Γ (cls u) (d n)) (fNE u n))
    (hSO : ∀ u n, IsSO Γ τ (restrict Γ (cls u) (d n)) (fSO u n)) (u : Fin m) :
    Tendsto (fun n => cost Γ τ (fNE u n) / cost Γ τ (fSO u n)) atTop (𝓝 1) ∧
    ∀ (dInf : Fin Γ.Sd → ℝ) (τInf : Fin Γ.J → ℝ → ℝ≥0∞),
      IsLimitGame Γ τ (cls u) (fun n => restrict Γ (cls u) (d n)) (g u) dInf τInf →
      ∀ fInf : Fin Γ.R → ℝ, IsLimNE Γ τInf dInf fInf →
        Tendsto (fun n => cost Γ τ (fNE u n) /
            (totalDemand Γ (restrict Γ (cls u) (d n)) * g u n)) atTop
          (𝓝 (limCost Γ τInf fInf).toReal) := by sorry

end LimitPoA.RegVar
