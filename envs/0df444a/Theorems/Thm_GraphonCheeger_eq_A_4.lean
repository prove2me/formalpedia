-- Prove2me | Theorems.Thm_GraphonCheeger_eq_A_4
-- name    : GraphonCheeger.eq_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:49:57.152267+00:00
-- url     : https://prove2.me/theorems/0efacf3b-76eb-4abd-b2cd-27d92206f453
-- title:
--   (A.4): the cut norm as a supremum over $[0,1]$-valued functions
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and $F$ an integrable function on $\Omega^2$. Then
--
--   $$\|F\|_\square=\sup_{0\le f,g\le1}\Bigl|\iint_{\Omega^2}F(x,y)\,f(x)\,g(y)\,d\mu(x)\,d\mu(y)\Bigr|,$$
--
--   the supremum over all measurable $f,g:\Omega\to[0,1]$.
--
--   This form of the cut norm is what makes it control the colouring functionals $C(W,\psi)$ and $m(W,\psi)$, whose integrands are $W$ times products of $[0,1]$-valued weights.
--
--   Differences from the source: none.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Appendix A, (A.4), p.81

import Mathlib
import Definitions.Def_GraphonCheeger_cutDist

open MeasureTheory

namespace GraphonCheeger

/-- (A.4), Appendix A, p.81 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for an integrable `F` on `Ω²`,
`‖F‖_□ = sup_{0 ≤ f, g ≤ 1} |∬ F(x, y) f(x) g(y) dµ(x) dµ(y)|`, the supremum over all measurable
`f, g : Ω → [0, 1]`. -/
theorem eq_A_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → Ω → ℝ) (hF : Integrable (fun p : Ω × Ω => F p.1 p.2) (μ.prod μ)) :
    cutNorm μ F = sSup {r : ℝ | ∃ f g : Ω → ℝ, Measurable f ∧ Measurable g ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
      r = |∫ p, F p.1 p.2 * f p.1 * g p.2 ∂(μ.prod μ)|} := by sorry

end GraphonCheeger
