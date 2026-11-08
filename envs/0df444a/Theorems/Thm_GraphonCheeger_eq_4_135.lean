-- Prove2me | Theorems.Thm_GraphonCheeger_eq_4_135
-- name    : GraphonCheeger.eq_4_135
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:20.695987+00:00
-- url     : https://prove2.me/theorems/4a708e3b-68fa-41a0-bc07-bd100557630c
-- title:
--   (4.135): $W\in\mathcal W_c$ iff $\int_A k_W\,d\mu\ge c\,\mu(A)$ for every measurable $A$
-- statement:
--   Let $W$ be a graphon on a probability space $(\Omega,\mathcal F,\mu)$ and $c\in[0,1]$. Then $W\in\mathcal W_c$ if and only if
--
--   $$m(W,\mathbf 1_A)=\int_Ak_W(x)\,d\mu(x)\ge c\,\mu(A)\qquad\text{for every measurable }A\subseteq\Omega .$$
--
--   This integrated form of the degree condition is stable under limits in the cut norm, which is how the class $\mathcal W_c$ is shown to be closed.
--
--   Differences from the source: none.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Definition 4.28, (4.135), p.48

import Mathlib
import Definitions.Def_GraphonCheeger_InWc

open MeasureTheory

namespace GraphonCheeger

/-- (4.135), Definition 4.28, p.48 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for a graphon `W` on `(Ω, F, µ)`, `W ∈ W_c` iff
`m(W, 1_A) = ∫_A k_W dµ ≥ c µ(A)` for every measurable `A ⊆ Ω`.

**Formalization Note.** `c ∈ [0, 1]` is the range of Definition 4.28. -/
theorem eq_4_135 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    InWc μ W c ↔
      ∀ A : Set Ω, MeasurableSet A → c * (μ A).toReal ≤ ∫ x in A, degFun μ W x ∂μ := by sorry

end GraphonCheeger
