-- Prove2me | Theorems.Thm_JHolomorphic_contDiffOn_of_hasWeakPartialsOn_of_add_add_eq_zero
-- name    : JHolomorphic.contDiffOn_of_hasWeakPartialsOn_of_add_add_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:21:12.443219+00:00
-- url     : https://prove2.me/theorems/221096d9-abdf-4ba6-bba2-a229bed811f1
-- title:
--   Weak solutions of a semilinear Cauchy–Riemann equation are smooth
-- statement:
--   Let $F$ be a finite-dimensional real vector space with a linear complex structure $J_0$ ($J_0^2=-1$), let $m:\mathbb C\times F\to F$ be $C^\infty$, $q>2$, and $U\subseteq\mathbb C$ open. Let $u:U\to F$ be continuous with weak partial derivatives $u_s,u_t\in L^q_{\mathrm{loc}}(U)$ satisfying
--   $$u_s+J_0\,u_t+m(z,u)=0\qquad\text{a.e. on }U .$$
--   Then $u$ is $C^\infty$ on $U$.
--
--   This is interior regularity for semilinear first-order Cauchy–Riemann equations with a constant complex structure and a smooth zeroth-order term, as they arise for perturbed holomorphic curves.
--
--   Formalization Note: `HasWeakPartialsOn U u us ut` (platform definition) says `us`, `ut` are the weak $\partial_s$, $\partial_t$ derivatives of `u` on `U` ($z=s+it$); local $L^q$ is `MemLp … (volume.restrict K)` for compact `K ⊆ U`.
-- source:
--   Standard elliptic regularity (cf. McDuff–Salamon, J-holomorphic curves, App. B)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Set
open scoped ContDiff ENNReal

/-- Let `F` be a finite-dimensional real normed space with a linear complex structure `J₀F`,
`m : ℂ → F → F` jointly `C^∞`, `q > 2` and `U ⊆ ℂ` open. Let `u` be continuous on `U` with weak
partial derivatives `us`, `ut` on `U` lying in `L^q` on every compact subset of `U`. If
`us + J₀F ut + m(z, u) = 0` almost everywhere on `U`, then `u` is `C^∞` on `U`. -/
theorem contDiffOn_of_hasWeakPartialsOn_of_add_add_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (J₀F : F →L[ℝ] F) (hJ : ∀ y, J₀F (J₀F y) = -y)
    (m : ℂ → F → F) (hm : ContDiff ℝ ∞ (fun x : ℂ × F => m x.1 x.2))
    (q : ℝ) (hq : 2 < q) (U : Set ℂ) (hU : IsOpen U) (u us ut : ℂ → F)
    (hu : ContinuousOn u U) (hw : HasWeakPartialsOn U u us ut)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp us (ENNReal.ofReal q) (volume.restrict K) ∧ MemLp ut (ENNReal.ofReal q) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J₀F (ut z) + m z (u z) = 0) :
    ContDiffOn ℝ ∞ u U := by
  sorry

end JHolomorphic
