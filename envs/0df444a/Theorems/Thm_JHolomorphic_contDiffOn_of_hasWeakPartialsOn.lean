-- Prove2me | Theorems.Thm_JHolomorphic_contDiffOn_of_hasWeakPartialsOn
-- name    : JHolomorphic.contDiffOn_of_hasWeakPartialsOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:49:02.39063+00:00
-- url     : https://prove2.me/theorems/a6492427-0c8b-49e4-a122-2d6958a9d71a
-- title:
--   Maps with $W^{1,p}_{\mathrm{loc}}$ weak partial derivatives, $p>2$, on a planar domain are $C^1$
-- statement:
--   Let $p>2$, let $E$ be a finite-dimensional real normed space and let $U\subseteq\mathbb{C}$ be open. Let $u:\mathbb{C}\to E$ be continuous on $U$ with weak partial derivatives $u_s,u_t$ on $U$, and suppose that $u_s$ and $u_t$ have weak partial derivatives $u_{ss},u_{st}$ and $u_{ts},u_{tt}$ on $U$, where $u_s,u_t,u_{ss},u_{st},u_{ts},u_{tt}$ all lie in $L^p(K)$ for every compact $K\subseteq U$ (so $u_s,u_t\in W^{1,p}_{\mathrm{loc}}(U)$). Then $u$ is continuously differentiable on $U$, and its classical partial derivatives $Du(z)\,1$ and $Du(z)\,i$ agree with $u_s(z)$ and $u_t(z)$ for almost every $z\in U$.
--
--   This is a two-dimensional regularity statement for Sobolev maps above the critical exponent, used to pass from weak to classical derivatives.
--
--   **Formalization Note** Weak partial derivatives are in the sense of `HasWeakPartialsOn` (testing against real $C^\infty$ functions with compact support in $U$), and $L^p(K)$ is `MemLp · (ENNReal.ofReal p) (volume.restrict K)`. $C^1$ on $U$ is `ContDiffOn ℝ 1 u U`; the classical partials are `fderiv ℝ u z 1` and `fderiv ℝ u z Complex.I`, and "almost every $z\in U$" is `∀ᵐ z ∂(volume.restrict U)`.
-- source:
--   Standard (Sobolev regularity above the critical exponent in dimension two; cf. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §2.5).

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

/-- Let `p > 2` and let `U ⊆ ℂ` be open. If `u : ℂ → E` is continuous on `U` and has weak
partial derivatives `uₛ`, `uₜ` on `U` which themselves have weak partial derivatives on `U`, all
of them in `L^p(K)` for every compact `K ⊆ U`, then `u` is `C¹` on `U` and its classical partial
derivatives `Du(z) 1`, `Du(z) i` agree with `uₛ`, `uₜ` almost everywhere on `U`. -/
theorem contDiffOn_of_hasWeakPartialsOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) (U : Set ℂ) (hU : IsOpen U)
    (u us ut uss ust uts utt : ℂ → E) (hu : ContinuousOn u U)
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U us uss ust)
    (h3 : HasWeakPartialsOn U ut uts utt)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ut (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp uss (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ust (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp uts (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp utt (ENNReal.ofReal p) (volume.restrict K)) :
    ContDiffOn ℝ 1 u U ∧
      ∀ᵐ z ∂(volume.restrict U), fderiv ℝ u z 1 = us z ∧ fderiv ℝ u z Complex.I = ut z := by
  sorry

end JHolomorphic
