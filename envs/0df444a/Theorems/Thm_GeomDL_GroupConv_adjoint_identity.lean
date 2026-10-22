-- Prove2me | Theorems.Thm_GeomDL_GroupConv_adjoint_identity
-- name    : GeomDL.GroupConv.adjoint_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:27.337356+00:00
-- url     : https://prove2.me/theorems/4bb16964-5df9-4efc-bfdc-ad909a14a180
-- title:
--   §4.3, p. 41 — pairing a transformed filter equals pairing the inversely transformed signal
-- statement:
--   Let $G$ act transitively and measurably on $\Omega$, and let $\mu$ be invariant under this action. For real-valued signals $x$ and $\theta$ on $\Omega$ and $g\in G$,
--
--   $$
--   \langle x,\rho(g)\theta\rangle_\mu
--   =\langle\rho(g^{-1})x,\theta\rangle_\mu.
--   $$
--
--   This is the matching identity used in the book's group-convolution equivariance calculation.
--
--   **Formalization Note** The action on signals is $(\rho(g)x)(u)=x(g^{-1}\cdot u)$. The transitivity hypothesis records the standing homogeneous-domain assumption stated on p. 43. Measurability of the group action and invariance of $\mu$ make the change of variables valid. No integrability assumption is added: the equality also holds for Lean's zero value for a nonintegrable integral.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.3, p. 41, sentence beginning 'The key observation'

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

namespace GeomDL.GroupConv

universe u v

/-- §4.3, p. 41: matching a transformed filter equals matching the inversely transformed signal. -/
theorem adjoint_identity {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [MeasurableSMul G Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.SMulInvariantMeasure G Ω μ]
    (htrans : ∀ a b : Ω, ∃ k : G, k • a = b)
    (g : G) (x θ : Ω → ℝ) :
    signalPairing μ x (signalAction g θ) =
      signalPairing μ (signalAction g⁻¹ x) θ := by sorry

end GeomDL.GroupConv
