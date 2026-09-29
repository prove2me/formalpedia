-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_psi_defines_process
-- name    : MultiperiodRisk.Bellman.psi_defines_process
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:05:17.133298+00:00
-- url     : https://prove2.me/theorems/51cb09f8-bfe1-43c5-9a6b-c4a38134db95
-- title:
--   Theorem 4.2, first sentence — $(\Psi_\sigma(X))_\sigma$ defines a process
-- statement:
--   Let $\mathcal P$ be a closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, with $\mathcal P^e\ne\emptyset$, and let $X$ be a value process. For every stopping time $\sigma$ with values in $\{0,\dots,N\}$,
--   $$
--   \Psi_\sigma(X)(\omega)=\Psi_{\sigma(\omega)}(X)(\omega)\quad\text{for }\mathbb P_0\text{-a.e. }\omega,
--   $$
--   i.e. $\Psi_\sigma(X)=\sum_{t=0}^{N}\mathbf 1_{\{\sigma=t\}}\Psi_t(X)$ a.s.
--
--   Thus the family $(\Psi_\sigma(X))_\sigma$ indexed by stopping times is the process $n\mapsto\Psi_n(X)$ evaluated at stopping times, which is what the paper means by "defines a process $\Psi(X)$". It holds for every set of test probabilities.
--
--   **Formalization Note** The statement holds without stability.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, Theorem 4.2, first sentence

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Theorem 4.2, first sentence: the family `(Ψ_σ(X))_σ` defines a process, i.e. the value
at a stopping time `σ` is the process `n ↦ Ψ_n(X)` evaluated at time `σ(ω)`. -/
theorem psi_defines_process {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    Psi D X σ hσ.1 =ᵐ[P₀] fun ω =>
      ∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0 := by sorry

end MultiperiodRisk.Bellman
