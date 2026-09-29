-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_psiBar_le_psi
-- name    : MultiperiodRisk.Bellman.psiBar_le_psi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:04:48.78082+00:00
-- url     : https://prove2.me/theorems/8986b38b-d1d3-441e-bea3-f777ecfbc61e
-- title:
--   Proof of Theorem 4.2, step (1) — $\Psi\ge\bar\Psi$
-- statement:
--   Let $\mathcal P$ be a closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, with $\mathcal P^e\ne\emptyset$ (no stability is assumed), and let $X$ be a value process. Then for every $0\le n\le N$,
--   $$
--   \bar\Psi_n(X)\le\Psi_n(X)\quad\mathbb P_0\text{-a.s.}
--   $$
--
--   This inequality, combined with Theorem 4.1, shows that whenever $\Psi(X)$ is a submartingale under every test probability it coincides with $\bar\Psi(X)$; it is the first step of the proof of Theorem 4.2.
--
--   **Formalization Note** $\Psi_n(X)$ is $\Psi$ at the constant stopping time $n$.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, pp. 11–12, §4.2, proof of Theorem 4.2, step (1)

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Proof of Theorem 4.2, step (1): `Ψ ≥ Ψ̄` for every set of test probabilities. -/
theorem psiBar_le_psi {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X) :
    ∀ n ≤ N, PsiBar D X n ≤ᵐ[P₀] PsiN D X n := by sorry

end MultiperiodRisk.Bellman
