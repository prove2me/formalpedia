-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_radial_primitive_derivatives
-- name    : NoHair.Weyl.kerr_radial_primitive_derivatives
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:24:02.150303+00:00
-- url     : https://prove2.me/theorems/bd3adc34-f397-4a2b-993f-dcdcb9f9a914
-- title:
--   First-order radial identities for the Kerr angular shift and conformal factor
-- statement:
--   In the open Weyl half-plane, let $r=m+x$, where $x$ is the mean distance to the two endpoints, $c=z/x$, $B=1-c^2$, $D=x^2-(m^2-a^2)c^2$, and $P=(r^2+a^2)^2-a^2\Delta B$. The coefficient $L=BP/D$ is positive. The functions $W=-2mra/P$ and $H=\tfrac12\log L-s$ are continuously differentiable. Their derivatives in $s=\log\rho$ at fixed $z$ are, respectively, the shift rate and the conformal rate obtained from the Kerr Ernst norm and twist. These differential identities hold before fixing the constants of integration at infinity.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, equations (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §§6.4–6.7, https://arxiv.org/abs/0806.0016. The logarithmic radial variable is that of the mission.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_radial_primitive_derivatives (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    let k := Real.sqrt (m^2-a^2)
    let x := prolateRadius k
    let r := fun p => m+x p
    let c := fun p : OrbitPoint => p.2/x p
    let B := fun p => 1-c p^2
    let P := fun p => (r p^2+a^2)^2-a^2*kerrDelta m a (r p)*B p
    let D := fun p => x p^2-k^2*c p^2
    let W := fun p => -(2*m*r p*a)/P p
    let L := fun p => B p*P p/D p
    let H := fun p : OrbitPoint => Real.log (L p)/2-p.1
    (∀ p, 0 < L p) ∧ ContDiff ℝ 1 W ∧ ContDiff ℝ 1 H ∧
      ∀ s z : ℝ,
        HasDerivAt (fun t => W (t,z)) (shiftRate (kerrErnst m a) (s,z)) s ∧
        HasDerivAt (fun t => H (t,z)) (conformalRate (kerrErnst m a) (s,z)) s := by
  sorry

end NoHair.Weyl
