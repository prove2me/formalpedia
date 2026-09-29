-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor
-- name    : LanglandsTunnell.ArchPlace.fourierIntegral_mixedSpace_pureTensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/a05976ea-c0d3-5150-be2a-ae3d93859bfb
-- title:
--   Fourier transform of an archimedean pure tensor
-- statement:
--   Let $K$ be a number field, and write $r_2 =$ `InfinitePlace.nrComplexPlaces K` for the number of its complex places. Given a family $a$ of elements of $\mathbb{Z}/2$ indexed by the real places of $K$, a family $k$ of integers indexed by the complex places, and an additive character $\psi$ of the mixed space $K \otimes_{\mathbb{Q}} \mathbb{R} = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ with values in $\mathbb{C}$, assume that $\psi(v) = e^{2\pi i \,\mathrm{tr}_{\mathbb{R}}(v)}$ for every $v$, where $\mathrm{tr}_{\mathbb{R}}$ is the $\mathbb{R}$-algebra trace of the mixed space and $e^{2\pi i(\cdot)}$ is `Real.fourierChar`. Let $x$ be a point of the mixed space. Consider the pure tensor $\Phi(v) = \bigl(\prod_w v_{1,w}^{(a_w).\mathrm{val}} e^{-\pi v_{1,w}^2}\bigr)\cdot \prod_w \overline{v_{2,w}}^{\,(k_w)^{+}} v_{2,w}^{\,(-k_w)^{+}} e^{-2\pi \|v_{2,w}\|^2}$, the first product over real places and the second over complex places, where $(\cdot)^{+}$ denotes `Int.toNat`. Then the Fourier integral $\int \psi(-(v\cdot x))\,\Phi(v)\,dv$ against the volume measure on the mixed space equals $$\Bigl(\prod_w (-i)^{(a_w).\mathrm{val}}\Bigr)\Bigl(\prod_w (-i)^{|k_w|}\Bigr)\bigl(\tfrac12\bigr)^{r_2}\,\Bigl(\prod_w x_{1,w}^{(a_w).\mathrm{val}} e^{-\pi x_{1,w}^2}\Bigr)\prod_w \overline{x_{2,w}}^{\,(-k_w)^{+}} x_{2,w}^{\,(k_w)^{+}} e^{-2\pi\|x_{2,w}\|^2},$$ i.e. the same pure tensor with the complex modes $k_w$ replaced by $-k_w$.
--
--   This is the archimedean local computation in Tate's method for a number field: the Gaussian-type test functions of weight $a_w \in \{0,1\}$ at the real places and of angular mode $k_w$ at the complex places form a pure tensor that is an eigenvector of the Fourier transform on $K \otimes_{\mathbb{Q}} \mathbb{R}$, up to the explicit constant $(-i)^{\sum a_w + \sum |k_w|} 2^{-r_2}$ and the flip of the complex modes. It feeds the analytic continuation and functional equation of global Hecke $L$-functions and, through those, the construction of the pinned Hecke data used in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_ArchPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField LanglandsTunnell.ArchPlace

open scoped Classical in

theorem LanglandsTunnell.ArchPlace.fourierIntegral_mixedSpace_pureTensor
    (K : Type) [Field K] [NumberField K]
    (a : {w : InfinitePlace K // w.IsReal} → ZMod 2) (k : {w : InfinitePlace K // w.IsComplex} → ℤ)
    (ψ : AddChar (mixedEmbedding.mixedSpace K) ℂ)
    (hψ : ∀ v : mixedEmbedding.mixedSpace K,
      ψ v = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace K) v) : ℂ))
    (x : mixedEmbedding.mixedSpace K) :
    NumberField.AdelicFourier.fourierIntegral ψ volume
        (fun v => (∏ w, realTestFun (a w) (v.1 w)) * ∏ w, complexTestFun (k w) (v.2 w)) x
      = (∏ w, (-Complex.I) ^ (a w).val) * (∏ w, (-Complex.I) ^ (k w).natAbs)
          * (1 / 2 : ℂ) ^ InfinitePlace.nrComplexPlaces K
          * ((∏ w, realTestFun (a w) (x.1 w)) * ∏ w, complexTestFun (-k w) (x.2 w)) := by sorry
