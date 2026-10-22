-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
-- name    : JHolomorphic.HasWeakPartialsOn.ae_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:40:49.397821+00:00
-- url     : https://prove2.me/theorems/b3a7f966-c0b1-4502-b3f2-56c103dde6ce
-- title:
--   Weak partial derivatives on an open planar set are unique almost everywhere
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open and suppose that both $(u_s,u_t)$ and $(u_s',u_t')$ are weak partial derivatives of $u$ on $U$, all four maps being integrable on every compact subset of $U$. Then $u_s=u_s'$ and $u_t=u_t'$ almost everywhere on $U$.
--
--   **Formalization Note** $E$ (and $F$) are finite-dimensional real normed spaces and $U\subseteq\mathbb{C}$ is open. Weak partial derivatives are in the sense of `HasWeakPartialsOn` (testing against real $C^\infty$ functions with compact support in $U$, Bochner integrals over $\mathbb{C}$), and "almost every $z\in U$" is `∀ᵐ z ∂(volume.restrict U)`.
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

/-- Weak partial derivatives on an open set are unique almost everywhere. -/
theorem HasWeakPartialsOn.ae_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut us' ut' : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) (h' : HasWeakPartialsOn U u us' ut')
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn us K ∧ IntegrableOn ut K ∧ IntegrableOn us' K ∧ IntegrableOn ut' K) :
    ∀ᵐ z ∂(volume.restrict U), us z = us' z ∧ ut z = ut' z := by
  sorry

end JHolomorphic
