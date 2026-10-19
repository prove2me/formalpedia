-- Prove2me | Theorems.Thm_LimitPoA_RegVar_theorem_3_2
-- name    : LimitPoA.RegVar.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:28.771966+00:00
-- url     : https://prove2.me/theorems/38782127-c0e2-4105-bb9e-28be015909bd
-- title:
--   Theorem 3.2, p. 21 — asymptotic decomposition theorem: if Γ ≍ Γ|K₁ ⊕ ⋯ ⊕ Γ|K_m then PoA‾(d⁽ⁿ⁾) → 1 and PoA(d⁽ⁿ⁾) → 1
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, with cost functions in the class of §2.1 that are not identically zero on $(0,\infty)$, and let $(d^{(n)})_{n\in\mathbb N}$ be a decomposable sequence. If $\Gamma \asymp_{d^{(n)}} \Gamma_{|\mathcal K_1}\oplus\cdots\oplus\Gamma_{|\mathcal K_m}$, then
--   $$\lim_{n\to\infty}\overline{\mathrm{PoA}}(d^{(n)}) = 1 \quad\text{and}\quad \lim_{n\to\infty}\mathrm{PoA}(d^{(n)}) = 1.$$
--
--   This is the paper's central convergence result for sequences whose groups grow at comparable or separated rates.
--
--   **Formalization Note** The printed statement reads "$\overline{\mathrm{PoA}}(d^n) = 1$", without the limit. The prose on p. 21 ("It shows that $\lim_{n\to\infty}\overline{\mathrm{PoA}}(d^{(n)}) = 1$") and the proof in Appendix A.3 establish the limit, which is stated here. The decomposition's classes partition the groups (see the definition file).
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 21, Theorem 3.2 (proof Appendix A.3, pp. 38–43)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp

namespace LimitPoA.RegVar

open Filter Topology

/-- Theorem 3.2, p. 21 (asymptotic decomposition theorem): if `Γ ≍_{d^(n)} Γ|K_1 ⊕ ⋯ ⊕ Γ|K_m` for a
decomposable sequence, then `\overline{PoA}(d^(n)) → 1` and `PoA(d^(n)) → 1`. -/
theorem theorem_3_2 (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (d : ℕ → Fin Γ.Sd → ℝ) (hdec : IsDecomposable Γ Finset.univ d)
    (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) (g : Fin m → ℕ → ℝ)
    (hAD : IsAsymDecomp Γ τ Finset.univ d m cls g) :
    Tendsto (fun n => PoABar Γ τ cls (d n)) atTop (𝓝 1) ∧
      Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1) := by sorry

end LimitPoA.RegVar
