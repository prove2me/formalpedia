-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchPlace_tateFourier_complexTestFun_zero_self
-- name    : LanglandsTunnell.ArchPlace.tateFourier_complexTestFun_zero_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/4a0c96b9-08f8-525f-bd7e-58dcfd46de55
-- title:
--   The complex Gaussian is self-dual for the self-dual measure
-- statement:
--   Work on $\mathbb{C}$ with the additive character $\psi(z) = \exp\bigl(-(2\pi i (z + \bar z))\bigr)$, i.e. $\psi(z) = \exp(-4\pi i \,\mathrm{Re}\, z)$, which is `psiComplex`, and with the measure $2 \cdot \mathrm{volume}$, the scalar multiple of Lebesgue measure on $\mathbb{C}$ by the extended nonnegative real number $2$. The test function is `complexTestFun 0`, i.e. the value at $k = 0$ of $z \mapsto (\bar z)^{k^{+}} z^{(-k)^{+}} \exp(-(2\pi \lVert z\rVert^{2}))$, so here simply the Gaussian $z \mapsto \exp(-2\pi \lvert z\rvert^{2})$. The assertion is an equality of functions $\mathbb{C} \to \mathbb{C}$: the Tate–Fourier transform of this Gaussian, defined by $y \mapsto \int f(x)\,\psi(xy)\,\mathrm{d}(2\cdot\mathrm{volume})(x)$, is the Gaussian itself. Equivalently, for every $y \in \mathbb{C}$, $$2\int_{\mathbb{C}} \exp(-2\pi\lvert x\rvert^{2})\,\exp\bigl(-4\pi i\,\mathrm{Re}(xy)\bigr)\,\mathrm{d}x = \exp(-2\pi\lvert y\rvert^{2}),$$ the integral being taken against Lebesgue measure on $\mathbb{C} \cong \mathbb{R}^{2}$. There are no further hypotheses; the factor $2$ in the measure is exactly what makes the eigenvalue equal to $1$.
--
--   This is the local computation at a complex place in Tate's thesis: the standard Gaussian is a fixed point of the Fourier transform attached to $\psi$ once Haar measure is normalised to the self-dual choice, twice Lebesgue measure. It serves as the analytic input at the archimedean place of the local functional equation, and is used in [`LanglandsTunnell.Converse.exists_archDatumC_W_ne_zero`](thm.html#LanglandsTunnell.Converse.exists_archDatumC_W_ne_zero) to exhibit an archimedean datum with nonvanishing Whittaker-type value.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchPlace_tateFourier_complexTestFun_zero_self.lean

import Definitions.Def_LanglandsTunnell_ArchPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

theorem LanglandsTunnell.ArchPlace.tateFourier_complexTestFun_zero_self :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun 0) = complexTestFun 0 := by sorry
