-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_lemma_2_7
-- name    : MFGLiquidation.Equilibrium.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:19.818491+00:00
-- url     : https://prove2.me/theorems/a8eb586d-548e-4bef-b609-3e51ebc9103f
-- title:
--   Lemma 2.7 — continuation step: unique solvability of (2.11) passes from 𝔭 to 𝔭 + 𝔡 for a uniform 𝔡
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE and let $0<\gamma<\alpha\wedge\frac12$. There is $\mathfrak d_0>0$ such that for every $\mathfrak p\in[0,1]$ and every $\mathfrak d\in(0,\mathfrak d_0]$ with $\mathfrak p+\mathfrak d\le1$: if (2.11) with parameter $\mathfrak p$ is uniquely solvable in
--   $$\mathcal H_\alpha\times\mathcal H_\gamma\times D^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)\times L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R^m)\times L^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R^m)$$
--   for every data $f\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)$, then the same holds with parameter $\mathfrak p+\mathfrak d$.
--
--   Starting from Lemma 2.6 ($\mathfrak p=0$), finitely many steps of length $\mathfrak d_0$ reach $\mathfrak p=1$, which is the system (2.10) behind the equilibrium.
--
--   **Formalization Note** "$\mathfrak d>0$ small enough (independent of $\mathfrak p$ and $f$)" is the quantifier order $\exists\,\mathfrak d_0>0\ \forall\mathfrak p\ \forall\mathfrak d\le\mathfrak d_0$, with $f$ quantified inside unique solvability; $\mathfrak d_0$ may depend on the coefficients, $T$, $A$ and $\gamma$. The restriction $\mathfrak p+\mathfrak d\le1$ keeps the parameter in the range $[0,1]$ in which (2.11) is posed. Assumption 2.3 is the standing assumption of §§2–4.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 12, Lemma 2.7

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting
import Definitions.Def_MFGLiquidation_Equilibrium_Decoupled

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem lemma_2_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA)
    (γ : ℝ) (hγ0 : 0 < γ) (hγα : γ < D.alpha P) (hγ2 : γ < 1 / 2) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ d : ℝ, 0 < d → d ≤ d₀ → p + d ≤ 1 →
      UniquelySolvable211 hD A γ p → UniquelySolvable211 hD A γ (p + d) := by sorry

end MFGLiquidation.Equilibrium
