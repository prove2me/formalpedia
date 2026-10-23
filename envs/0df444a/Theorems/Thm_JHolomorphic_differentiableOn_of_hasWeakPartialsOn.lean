-- Prove2me | Theorems.Thm_JHolomorphic_differentiableOn_of_hasWeakPartialsOn
-- name    : JHolomorphic.differentiableOn_of_hasWeakPartialsOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T10:58:31.012814+00:00
-- url     : https://prove2.me/theorems/c79788f6-6208-46ea-bb2c-1bab154d77f4
-- title:
--   Continuous $W^{1,p}_{\mathrm{loc}}$ solutions of $\bar\partial f=0$ are holomorphic
-- statement:
--   Let $p>2$, let $U\subset\mathbb{C}$ be open, and let $f:U\to\mathbb{C}^n$ be continuous on $U$. Suppose $f$ has weak partial derivatives $f_s,f_t$ on $U$ (that is, $\int (\partial_s\varphi)\,f=-\int\varphi\,f_s$ and $\int(\partial_t\varphi)\,f=-\int\varphi\,f_t$ for every real $C^\infty$ function $\varphi$ with compact support in $U$), that $f,f_s,f_t\in L^p(K)$ for every compact $K\subset U$, and that
--   $$f_s+i\,f_t=0\quad\text{almost everywhere on }U.$$
--   Then $f$ is holomorphic on $U$.
--
--   This is the weak form of the Cauchy–Riemann equations for Sobolev maps: a continuous $W^{1,p}_{\mathrm{loc}}$ solution of $\bar\partial f=0$ is a genuine holomorphic map. It is the step that turns weak solutions of Cauchy–Riemann type equations into holomorphic objects.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`; the weak partials are expressed with `JHolomorphic.HasWeakPartialsOn U f fs ft` from the imported setting, local $L^p$ is `MemLp _ (ENNReal.ofReal p) (volume.restrict K)` for all compact `K ⊆ U`, and holomorphy is `DifferentiableOn ℂ f U`.
-- source:
--   Classical (weak Cauchy–Riemann equations); used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Complex.Conformal

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Let `p > 2` and `U ⊆ ℂ` open. A map `f : U → ℂⁿ` that is continuous on `U`, has weak partial
derivatives `fₛ`, `fₜ` on `U` with `f, fₛ, fₜ ∈ L^p(K)` for every compact `K ⊆ U`, and satisfies
`fₛ + i fₜ = 0` almost everywhere on `U`, is holomorphic on `U`. -/
theorem differentiableOn_of_hasWeakPartialsOn (n : ℕ) (p : ℝ) (hp : 2 < p) {U : Set ℂ}
    (hU : IsOpen U) (f fs ft : ℂ → EuclideanSpace ℂ (Fin n)) (hf : ContinuousOn f U)
    (hw : HasWeakPartialsOn U f fs ft)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp f (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp fs (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ft (ENNReal.ofReal p) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), fs z + Complex.I • ft z = 0) :
    DifferentiableOn ℂ f U := by
  sorry

end JHolomorphic
