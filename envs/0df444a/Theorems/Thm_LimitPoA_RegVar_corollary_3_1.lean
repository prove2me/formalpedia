-- Prove2me | Theorems.Thm_LimitPoA_RegVar_corollary_3_1
-- name    : LimitPoA.RegVar.corollary_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:24.738726+00:00
-- url     : https://prove2.me/theorems/1c0c84d3-f462-461f-a7ea-0e5395e17dc5
-- title:
--   Corollary 3.1, p. 23 — if the regular groups K_reg decompose, PoA(d⁽ⁿ⁾) → 1 along a regular sequence
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, with cost functions in the class of §2.1 that are not identically zero on $(0,\infty)$, and let $(d^{(n)})_{n\in\mathbb N}$ be a regular sequence with set $\mathcal K_{reg}$ of regular groups (those with $d^{(n)}_k \to \infty$). If the demand sequence $(d^{(n)}_{|\mathcal K_{reg}})_n$ is decomposable and $\Gamma_{|\mathcal K_{reg}} \asymp_{d^{(n)}_{|\mathcal K_{reg}}} \Gamma_{|\mathcal K_1}\oplus\cdots\oplus\Gamma_{|\mathcal K_m}$ for some subsets $\mathcal K_1,\dots,\mathcal K_m$ of $\mathcal K_{reg}$, then
--   $$\lim_{n\to\infty}\mathrm{PoA}(d^{(n)}) = 1.$$
--
--   The groups with bounded demand contribute only a negligible part of the cost, so the decomposition of the regular groups suffices.
--
--   **Formalization Note** As in Definition 3.5, the classes $\mathcal K_1,\dots,\mathcal K_m$ partition $\mathcal K_{reg}$.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 23, Corollary 3.1 (K_reg p. 22; proof Appendix A.4, p. 43)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp

namespace LimitPoA.RegVar

open Filter Topology

/-- Corollary 3.1, p. 23: for a regular sequence whose regular groups `K_reg` carry a decomposable
sequence and an asymptotic decomposition `Γ|K_reg ≍ Γ|K_1 ⊕ ⋯ ⊕ Γ|K_m`, `PoA(d^(n)) → 1`. -/
theorem corollary_3_1 (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (d : ℕ → Fin Γ.Sd → ℝ) (dInf : Fin Γ.Sd → ℝ) (hreg : IsRegular Γ d dInf)
    (hdec : IsDecomposable Γ (Kreg Γ d) (fun n => restrict Γ (Kreg Γ d) (d n)))
    (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) (g : Fin m → ℕ → ℝ)
    (hAD : IsAsymDecomp Γ τ (Kreg Γ d) (fun n => restrict Γ (Kreg Γ d) (d n)) m cls g) :
    Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1) := by sorry

end LimitPoA.RegVar
