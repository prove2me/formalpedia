-- Prove2me | Theorems.Thm_MFHeisGibbs_eq_27
-- name    : MFHeisGibbs.eq_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:04.293548+00:00
-- url     : https://prove2.me/theorems/4c3c72c5-c831-42ec-828d-d8de3f74ffd5
-- title:
--   (13), (27) — $\rho$ is stationary, $\mathcal L$ is KMS self-adjoint, $\mathrm{gap}(-\mathcal D)=\mathrm{gap}(-\mathcal L)$ equals both Rayleigh infima
-- statement:
--   Let $f$ satisfy (4), let $\sigma>0$, $0\le\beta<\infty$, $n\ge2$ and $\mathcal L\in\{\mathcal L_C,\mathcal L_D,\mathcal L_{F,\sigma}\}$. Then $\mathcal L^\dagger[\rho]=0$; $\mathcal L$ is self-adjoint for $\langle\cdot,\cdot\rangle_\rho$; the discriminant $\mathcal D$ is self-adjoint for the Hilbert–Schmidt inner product; $\mathrm{gap}(-\mathcal D)=\mathrm{gap}(-\mathcal L)$; and, when $\mathcal L$ has a scalar kernel,
--
--   $$\mathrm{gap}(-\mathcal L)=\inf_{X\ne0,\ \mathrm{Tr}(\rho X)=0}\frac{\langle X,-\mathcal L[X]\rangle_\rho}{\|X\|_\rho^2}=\inf_{\mathrm{Var}_\rho(X)>0}\frac{\mathcal E(X)}{\mathrm{Var}_\rho(X)} .$$
--
--   This links the spectral gap to the variational form in which all lower and upper bounds of the paper are proved.
--
--   Differences from the source:
--   - encoding: the equality (27), written with no hypothesis on the kernel → the two infima are stated when L has a scalar kernel; reason: p.50 says the variational gap is the spectral gap for 'only scalar fixed observables' and is zero otherwise; the goal gives the scalar kernel for these generators
--   - encoding: L_{F,σ} at β = 0, which the page defines as a limit → LFall, which is LF0 at β = 0; reason: literal (10) is the zero map at β = 0; see the milestone eq_101_113_limits
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (13), p.5 (PDF 6); (27), p.9 (PDF 10)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Gap
import Definitions.Def_MFHeisGibbs_KMS
import Definitions.Def_MFHeisGibbs_Mixing

open Matrix

namespace MFHeisGibbs

/-- **(13), (27)**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), pp.5, 9.
For `0 ≤ β < ∞` and `f` with (4): `ρ` is a fixed point of `L†`, `L` is KMS self-adjoint, the
discriminant `D` is Hilbert–Schmidt self-adjoint, `gap(−D) = gap(−L)`, and for `L` with a scalar kernel
`gap(−L)` is the infimum of each of the two Rayleigh quotients of (27).

**Formalization Note.** This links the spectral `specGap` of the goal to the variational form of the
page. Without the scalar kernel the variational form would vanish and differ from `specGap`, as p.50
notes ("otherwise this variational gap is zero"). The goal proves the scalar kernel for these `L`. -/
theorem eq_27 (f : ℝ → ℂ) (hf : IsKMSFilter f) (s : ℝ) (hs : 0 < s) (β : ℝ) (hβ : 0 ≤ β)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ L ∈ ({LC β f n, LD β f n, LFall β s f n} : Set (Module.End ℂ (Op n))),
      hsAdjoint L (rhoPow β 1 n) = 0 ∧
      (∀ X Y : Op n, kmsInner β X (L Y) = kmsInner β (L X) Y) ∧
      (∀ X Y : Op n, trace (Xᴴ * discriminant β L Y) = trace ((discriminant β L X)ᴴ * Y)) ∧
      specGap (discriminant β L) = specGap L ∧
      (ScalarKernel L →
        specGap L = sInf {r : ℝ | ∃ X : Op n, X ≠ 0 ∧ trace (rhoPow β 1 n * X) = 0 ∧
          r = dirichlet β L X / kmsNormSq β X} ∧
        specGap L = sectorGap β L Set.univ) := by sorry

end MFHeisGibbs
