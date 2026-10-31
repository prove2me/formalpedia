-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_theorem_2_11
-- name    : KallMayerSLP.GenConcave.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:35.017997+00:00
-- url     : https://prove2.me/theorems/6e51f1b2-256d-4e09-8799-66f6f3def145
-- title:
--   Theorem 2.11 — affine images of $\gamma$-concave distributions are $\gamma$-concave
-- statement:
--   Let $\xi$ be an $s$-dimensional random vector, $D$ a real $(r\times s)$ matrix, $d\in\mathbb R^r$, and $\zeta=D\xi+d$. If $\xi$ has a $\gamma$-concave distribution, then the distribution of $\zeta$ is also $\gamma$-concave.
--
--   No rank condition is placed on $D$. Applied to a vector of independent standard normal components, which has a log-concave law by Theorem 2.8, it shows that every (possibly degenerate) multivariate normal distribution is log-concave.
--
--   **Formalization Note** The law of $\xi$ is a measure $\mu$ on `Fin s → ℝ`, and the law of $\zeta$ is its image under $x\mapsto Dx+d$ on `Fin r → ℝ`.
--
--   Differences from the source:
--   - encoding: distribution of $\xi$ → a measure $\mu$ on $\mathbb R^s$ ($\gamma$-concavity includes being a probability measure); reason: every probability measure is the law of the identity map, same instances
--   - encoding: distribution of $\zeta=D\xi+d$ → the image measure of $\mu$ under $x\mapsto Dx+d$; reason: definition of the law of $\zeta$, same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 2.11, p.133 (PDF 143)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveMeasure

open MeasureTheory Matrix

namespace KallMayerSLP.GenConcave

/-- **Theorem 2.11** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2,
Theorem 2.11, p. 133, PDF p. 143). Let `ξ` be an `s`-dimensional random vector, `D` an
`(r × s)` matrix, and `ζ = Dξ + d`. If `ξ` has a `γ`-concave distribution then the
distribution of `ζ` is also `γ`-concave.

**Formalization Note.** The law of `ξ` is the measure `μ` on `ℝ^s = Fin s → ℝ`; the law of
`ζ` is its image `μ.map (x ↦ D x + d)` on `ℝ^r = Fin r → ℝ`. `D` is any real `r × s`
matrix (no rank condition) and `d ∈ ℝ^r`. -/
theorem theorem_2_11 {s r : ℕ} (γ : EReal) (μ : Measure (Fin s → ℝ))
    (D : Matrix (Fin r) (Fin s) ℝ) (d : Fin r → ℝ) (hμ : IsGammaConcaveMeasure γ μ) :
    IsGammaConcaveMeasure γ (μ.map (fun x : Fin s → ℝ => D *ᵥ x + d)) := by sorry

end KallMayerSLP.GenConcave
