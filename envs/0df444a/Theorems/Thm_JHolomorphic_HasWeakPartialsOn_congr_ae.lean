-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_congr_ae
-- name    : JHolomorphic.HasWeakPartialsOn.congr_ae
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:39:43.054705+00:00
-- url     : https://prove2.me/theorems/4d178e73-72fa-492b-bfd1-c2d6a6a682b6
-- title:
--   Weak partial derivatives are insensitive to changes on null sets
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open and let $u_s,u_t$ be weak partial derivatives of $u$ on $U$. If $u=u'$, $u_s=u_s'$ and $u_t=u_t'$ almost everywhere on $U$, then $u_s',u_t'$ are weak partial derivatives of $u'$ on $U$.
--
--   **Formalization Note** $E$ is a real normed space. Weak partial derivatives are in the sense of `HasWeakPartialsOn` (testing against real $C^\infty$ functions with compact support in $U$, Bochner integrals over $\mathbb{C}$), and "almost every $z\in U$" is `∀ᵐ z ∂(volume.restrict U)`.
-- source:
--   Standard (weak derivatives and distribution theory).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak partial derivatives on `U` may be changed on null subsets of `U`, as may the map
itself. -/
theorem HasWeakPartialsOn.congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} (hU : IsOpen U) {u us ut u' us' ut' : ℂ → E} (h : HasWeakPartialsOn U u us ut)
    (hu : ∀ᵐ z ∂(volume.restrict U), u z = u' z) (hs : ∀ᵐ z ∂(volume.restrict U), us z = us' z)
    (ht : ∀ᵐ z ∂(volume.restrict U), ut z = ut' z) : HasWeakPartialsOn U u' us' ut' := by
  sorry

end JHolomorphic
