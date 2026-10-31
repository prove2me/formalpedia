-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_proposition_4_6
-- name    : KallMayerSLP.CondExp.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:11.290858+00:00
-- url     : https://prove2.me/theorems/2489c1a9-fe6d-44db-8e34-46b0ccd3bf28
-- title:
--   Proposition 4.6 — $w_c^\alpha$ is jointly convex
-- statement:
--   Let $t(\xi)$ be an integrable $n$-dimensional random vector, $h(\xi)$ an integrable random variable, $\zeta(x,\xi)=t(\xi)^{\mathrm T}x-h(\xi)$ and $0<\alpha<1$. Then
--   $$
--   (x,z)\mapsto w_c^\alpha(x,z)=z+\frac{1}{1-\alpha}\,\mathbb E[(\zeta(x,\xi)-z)^+]
--   $$
--   is a convex function on $\mathbb R^n\times\mathbb R$.
--
--   Consequently the CVaR model (4.35) is a convex program for an arbitrary distribution of $\xi$.
--
--   **Formalization Note** Integrability is the standing assumption of §4.1, p.149, that the expected values of $T(\xi)$ and $h(\xi)$ exist.
--
--   Differences from the source:
--   - encoding: t(ξ), h(ξ) functions of a random vector ξ → maps t, h on the underlying probability space; reason: taking t ∘ ξ and h ∘ ξ recovers the book's form
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 4.6, p.162

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_wC

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- `w_c^α` is a convex function of the joint variables `(x, z)`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 4.6, p.162 (PDF 172).

**Formalization Note** Integrability of the components of `t` and of `h` is the assumption of §4.1
(p.149) that the expected values of `T(ξ)` and `h(ξ)` exist; for `ζ(x, ξ)` it is what puts every
`ζ(x, ·)` in `𝓛¹₁`, the domain of (4.32). `0 < α < 1` is the assumption of Proposition 4.5. -/
theorem proposition_4_6 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : Ω → Fin n → ℝ) (h : Ω → ℝ)
    (ht : ∀ i, Integrable (fun ω => t ω i) μ) (hh : Integrable h μ) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α < 1) :
    ConvexOn ℝ Set.univ (fun p : (Fin n → ℝ) × ℝ => wC μ t h α p.1 p.2) := by sorry

end KallMayerSLP.CondExp
