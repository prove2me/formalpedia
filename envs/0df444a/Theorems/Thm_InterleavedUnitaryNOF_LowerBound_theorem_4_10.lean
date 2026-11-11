-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_theorem_4_10
-- name    : InterleavedUnitaryNOF.LowerBound.theorem_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:29.537543+00:00
-- url     : https://prove2.me/theorems/a964f840-2226-42e8-871c-cfe3cbf1eeb1
-- title:
--   Theorem 4.10 — global conditional-overlap grid norm
-- statement:
--   There are universal constants $\lambda>1$ and $\kappa>0$. For every $m\ge1$, measurable Boolean $f:\mathcal Y\times\mathcal Z\to\{0,1\}$ and $g:\mathcal X\times\mathcal Z\to\{0,1\}$, and integer $d\ge2$,
--
--   $$\|\mathbb E_{\mu_1}[f(Y,Z)g(X,Z)\mid X,Y]\|_d\le\lambda^{1+2/d}\|f\|_{U(2,d)}\|g\|_{U(2,d)}+e^{-\kappa\sqrt m/d}.$$
--
--   Here $\mathcal X=\mathcal Y=SU(m)^4$, $\mathcal Z=SU(m)^2$, all unconditioned norms use normalized product Haar measure, and the conditional law samples $E_1$ Haar and sets $E_2=(PE_1Q)^{-1}$, with $P=A_1B_1C_1D_1$ and $Q=A_2B_2C_2D_2$. The estimate covers all measurable factors.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: conditional expectation given X,Y → the explicit Haar E₁ sampling kernel with E₂=(PE₁Q)⁻¹; reason: p.15 identifies this conditional law, avoiding conditioning by division on a null event
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Theorem 4.10, printed p.14 = PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem theorem_4_10 : ∃ lam κ : ℝ, 1 < lam ∧ 0 < κ ∧
    ∀ (m : ℕ) [NeZero m] (f g : Quart m × Duo m → Bool),
      Measurable f → Measurable g → ∀ (d : ℕ), 2 ≤ d →
      lpNorm ((haarPower m 4).prod (haarPower m 4)) (conditionalOverlap f g) d ≤
        Real.rpow lam (1+2/(d : ℝ)) *
          gridNorm (haarPower m 4) (haarPower m 2) (bval ∘ f) d *
          gridNorm (haarPower m 4) (haarPower m 2) (bval ∘ g) d +
        Real.exp (-κ*Real.sqrt m/(d : ℝ)) := by sorry

end InterleavedUnitaryNOF.LowerBound
