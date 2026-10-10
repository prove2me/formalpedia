-- Prove2me | Theorems.Thm_OAI_Erdos3_goodScalarKernelTuple_anisotropic_error
-- name    : OAI.Erdos3.goodScalarKernelTuple_anisotropic_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:15:07.003715+00:00
-- url     : https://prove2.me/theorems/0df80782-27fe-4837-b6a8-8e6c3948f90c
-- title:
--   Local law for the anisotropic spatial output of a good scalar-cube kernel tuple
-- statement:
--   Let $I,J,N$ be finite types with decidable equality, $L,B\in\mathbb N$ with $L>0$, $s\colon I\hookrightarrow J$, and $x\colon J\to$ `IntegerScalarCubeBox I L` (each $x_j$ a function $\mathrm{Option}\,I\to\{-L,\dots,L-1\}$); let $M_x=$ `scalarCubeDifferenceMatrix x` be the integer matrix $(x_j(\mathrm{some}\ i))_{i\in I,j\in J}$. Let $\mathrm{root}\colon J\to\mathbb Z$, $C\in\mathbb Z^{(\mathrm{Unit}\oplus I)\times N}$, $Q\colon N\to\mathbb R$, and reals $A,R,\kappa,C_0,\rho,\xi$ with $A,R,\kappa,\rho>0$. Assume `GoodScalarKernelTuple s κ B x`: $\kappa<|\det((M_x)_{i,s(i')})/L^{|I|}|$, and $a\mathbb Z^I$ is contained in the column span of $M_x$ for some natural number $0<a\le B$. Assume further $1\le C_0$, $L\le C_0$, $|\mathrm{root}_j|\,R\le A$ and $|\mathrm{root}_j|\le C_0$ for all $j$, $Q_j>0$ for all $j$, $0\le\xi\le1$, $|C_{ij}|\,Q_j\le\xi\,\sigma_i$ for all $i,j$, where $\sigma=$ `physicalSpatialOutputScale I A R L` is $A$ on the $\mathrm{Unit}$ coordinate and $LR$ on the others, $\rho\le A$, $\rho\le R$, $\rho\le Q_j$ for all $j$, and `anisotropicSpatialMeshThreshold s N C₀` $\le\rho$ (an explicit real constant). Let $A_0=$ `selectedSpatialPivot root M_x s` (whose determinant is nonzero under these hypotheses, `goodScalarKernelTuple_spatial_det_ne_zero`) and $B_0=$ `selectedSpatialFreeColumns root M_x s`, the pivot and free columns of $\begin{pmatrix}1&\mathrm{root}\\0&M_x\end{pmatrix}$ along $s$. Then for every $v\in\mathbb Z^{\mathrm{Unit}\oplus I}$,
--   $$\Big|\Big(\prod_i\sigma_i\Big)\,\pi(v)-\texttt{maskedIntegerImageDensity}\ A_0\ [B_0\,|\,C]\ \sigma\ g\ v\Big|\le\texttt{anisotropicSpatialError}\ s\ N\ B\ \kappa\ C_0\ \rho\ \xi .$$
--   Here $\pi=$ `anisotropicSpatialOutputLaw root M_x C A R Q …` is the law of $\big[\begin{smallmatrix}1&\mathrm{root}\\0&M_x\end{smallmatrix}\,\big|\,C\big]\,z\in\mathbb Z^{\mathrm{Unit}\oplus I}$ when $z\in\mathbb Z^{(\mathrm{Unit}\oplus J)\oplus N}$ has probability proportional to $\prod_c\phi(z_c/S_c)$ with scales $S=A$ on $\mathrm{Unit}$, $R$ on $J$ and $Q$ on $N$ ($\phi=$ `smoothProbabilityProfile`); $[X\,|\,Y]$ is `Matrix.fromCols`; `maskedIntegerImageDensity A B P f v` is the index of the lattice `pivotFullImage A B` (the sum of the column spans) times $f(v_i/P_i)$ if $v$ lies in that lattice, and $0$ otherwise; $g=$ `anisotropicSpatialKernelDensity s root M_x _ A R L …`, a real function on $\mathbb R^{\mathrm{Unit}\oplus I}$ (a `normalizedFiberDensity` built from $A_0,B_0$ and the scales); and `anisotropicSpatialError s N B κ C₀ ρ ξ` is an explicit real constant built from `normalizedFiberErrorConstant` and `spatialKernelErrorConstant`.
--
--   Lean: `OAI.Erdos3.goodScalarKernelTuple_anisotropic_error` in `lean/OAI/Combinatorics/Progressions/Linear/AnisotropicGoodKernelComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B089` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AnisotropicGoodKernelComparison.lean#L145

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B089

namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem goodScalarKernelTuple_anisotropic_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} (hL : 0 < L) (s : I ↪ J) (x : J → IntegerScalarCubeBox I L)
    (root : J → ℤ) (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    {A R κ C₀ ρ ξ : ℝ} (hA : 0 < A) (hR : 0 < R) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple s κ B x) (hC₀ : 1 ≤ C₀) (hLC : (L : ℝ) ≤ C₀)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hrC : ∀ j, |(root j : ℝ)| ≤ C₀)
    (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i)
    (hscaleA : ρ ≤ A) (hscaleR : ρ ≤ R) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hmesh : anisotropicSpatialMeshThreshold s N C₀ ≤ ρ) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero s x root hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale I A R L i) *
        (anisotropicSpatialOutputLaw root (scalarCubeDifferenceMatrix x) C A R Q hA hR hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C)
        (physicalSpatialOutputScale I A R L)
        (anisotropicSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hp A R L
          hA hR (Nat.cast_pos.mpr hL)) v| ≤ anisotropicSpatialError s N B κ C₀ ρ ξ := by
  sorry

end Erdos3
end
end OAI
