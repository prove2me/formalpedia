-- Prove2me | Theorems.Thm_LimitPoA_RegVar_lemma_3
-- name    : LimitPoA.RegVar.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:39.884448+00:00
-- url     : https://prove2.me/theorems/435e5dfc-6f64-41f3-964a-bc07a98421a1
-- title:
--   Lemma 3, p. 13 — asymptotically well designed ⇔ PoA → 1 along every regular sequence ⇔ along a subsequence of every regular sequence
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, with cost functions in the class of §2.1 that are not identically zero on $(0,\infty)$. The following statements are equivalent.
--
--   1. $\Gamma$ is asymptotically well designed.
--   2. $\lim_{n\to\infty}\mathrm{PoA}(d^{(n)}) = 1$ for all regular sequences $(d^{(n)})_{n\in\mathbb N}$.
--   3. For each regular sequence $(d^{(n)})_{n\in\mathbb N}$ there is an infinite subsequence $(n_i)_{i\in\mathbb N}$ with $\lim_{i\to\infty}\mathrm{PoA}(d^{(n_i)}) = 1$.
--
--   The lemma reduces the convergence of the PoA along arbitrary unbounded sequences to convergence along suitable subsequences of regular sequences.
--
--   **Formalization Note** A regular sequence is given together with its limit distribution $d^{(\infty)}$; an infinite subsequence is a strictly increasing map $\varphi : \mathbb N \to \mathbb N$. The equivalence is stated as `List.TFAE`.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 13, Lemma 3

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit

namespace LimitPoA.RegVar

open Filter Topology

/-- Lemma 3, p. 13: (a) asymptotically well designed ⇔ (b) `PoA(d^(n)) → 1` along every regular
sequence ⇔ (c) every regular sequence has an infinite subsequence along which `PoA → 1`. -/
theorem lemma_3 (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0) :
    List.TFAE
      [IsAsymptoticallyWellDesigned Γ τ,
       ∀ (d : ℕ → Fin Γ.Sd → ℝ) (dInf : Fin Γ.Sd → ℝ), IsRegular Γ d dInf →
         Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1),
       ∀ (d : ℕ → Fin Γ.Sd → ℝ) (dInf : Fin Γ.Sd → ℝ), IsRegular Γ d dInf →
         ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => PoA Γ τ (d (φ i))) atTop (𝓝 1)] := by sorry

end LimitPoA.RegVar
