-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_psi_eq_fromStop_add_prev
-- name    : MultiperiodRisk.Bellman.psi_eq_fromStop_add_prev
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:05:54.941911+00:00
-- url     : https://prove2.me/theorems/17acd2d0-df65-42c7-8ca7-50039f35ddc3
-- title:
--   Remark after Theorem 4.2 — $\Psi_\tau(X)=\Psi_\tau({}^\tau X)+X_{\tau-1}$
-- statement:
--   Let $\mathcal P$ be a closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, with $\mathcal P^e\ne\emptyset$, let $X$ be a value process and $\tau$ a stopping time with values in $\{0,\dots,N\}$. Then
--   $$
--   \Psi_\tau(X)=\Psi_\tau({}^\tau X)+X_{\tau-1}\quad\mathbb P_0\text{-a.s.},
--   $$
--   where ${}^\tau X_n=\mathbf 1_{\{n\ge\tau\}}(X_n-X_{\tau-1})$ and $X_{-1}=0$.
--
--   The identity separates the part of $X$ already known at $\tau$ from the part still at risk; it is used in step (4) of the proof of Theorem 4.2 and in Theorem 4.3.
--
--   **Formalization Note** The paper leaves $X_{-1}$ undefined; the convention $X_{-1}=0$ is used. No stability is assumed.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, §4.2, Remark after Theorem 4.2, last identity

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_StopOps

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Remark after Theorem 4.2: `Ψ_τ(X) = Ψ_τ(^τX) + X_{τ-1}` (with `X_{-1} = 0`). -/
theorem psi_eq_fromStop_add_prev {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    Psi D X τ hτ.1 =ᵐ[P₀] fun ω => Psi D (fromStop X τ) τ hτ.1 ω + Xprev X τ ω := by sorry

end MultiperiodRisk.Bellman
