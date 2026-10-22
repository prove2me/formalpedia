-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq_mixed
-- name    : JHolomorphic.HasWeakPartialsOn.ae_eq_mixed
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:42:30.470027+00:00
-- url     : https://prove2.me/theorems/fb65f6fa-e385-4f40-bfe6-6eca3d2ae407
-- title:
--   Weak mixed partial derivatives on a planar domain agree
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open. Suppose $u$ has weak partial derivatives $u_s,u_t$ on $U$, $u_s$ has weak partial derivatives $u_{ss},u_{st}$ on $U$, and $u_t$ has weak partial derivatives $u_{ts},u_{tt}$ on $U$, where $u_{st}$ and $u_{ts}$ are integrable on every compact subset of $U$. Then $u_{st}=u_{ts}$ almost everywhere on $U$.
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

/-- Weak mixed partial derivatives agree: if `u` has weak partials `uₛ`, `uₜ` on an open set `U`,
and these have weak partials `(uₛₛ, uₛₜ)` and `(uₜₛ, uₜₜ)`, then `uₛₜ = uₜₛ` almost everywhere
on `U`. -/
theorem HasWeakPartialsOn.ae_eq_mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut uss ust uts utt : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) (hs : HasWeakPartialsOn U us uss ust)
    (ht : HasWeakPartialsOn U ut uts utt)
    (hint : ∀ K ⊆ U, IsCompact K → IntegrableOn ust K ∧ IntegrableOn uts K) :
    ∀ᵐ z ∂(volume.restrict U), ust z = uts z := by
  sorry

end JHolomorphic
