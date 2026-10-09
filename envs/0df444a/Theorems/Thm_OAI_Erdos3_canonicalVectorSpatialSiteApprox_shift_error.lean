-- Prove2me | Theorems.Thm_OAI_Erdos3_canonicalVectorSpatialSiteApprox_shift_error
-- name    : OAI.Erdos3.canonicalVectorSpatialSiteApprox_shift_error
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T19:13:59.350352+00:00
-- url     : https://prove2.me/theorems/9faefc1a-98e9-4ac4-b257-be8151604334
-- title:
--   Shifted spatial mass products are close to canonical spatial site approximations
-- statement:
--   Let $D,I,J,N$ be finite types ($I,J$ with decidable equality), $s\colon I\hookrightarrow J$ an embedding, $\mathrm{root}\colon J\to\mathbb Z$ and $M\in\mathbb Z^{I\times J}$, and let $A_0=$ `selectedSpatialPivot root M s` be the $(\mathrm{Unit}\oplus I)$-square integer matrix $\begin{pmatrix}1&(\mathrm{root}_{s(i)})_i\\0&(M_{i,s(i')})\end{pmatrix}$, assumed to have $\det A_0\ne0$; let $B_0=$ `selectedSpatialFreeColumns root M s` be the matrix with rows indexed by $\mathrm{Unit}\oplus I$ and columns by the unselected columns $j\notin s(I)$ (`UnselectedColumn s`), with entries $\mathrm{root}_j$ in the $\mathrm{Unit}$ row and $M_{i,j}$ in row $i$. Let $C_d,R_d\in\mathbb Z^{(\mathrm{Unit}\oplus I)\times N}$ and $H_d,T_d>0$ for $d\in D$, and reals $W,L,\kappa,E,\delta,b,r$ with $W\ge0$, $L>0$, $L\ge1$, $\kappa>0$, $H_d=(1+W)T_d$ for all $d$, $|\mathrm{root}_j|\le1+W$, $|M_{ij}|\le L$, and $\kappa\le|\det(M_{i,s(i')}/L)_{i,i'}|$. Let $m\ne0$ be a natural number with $m\mathbb Z^{\mathrm{Unit}\oplus I}\subseteq$ `pivotFullImage A₀ B₀` (the sum of the column spans of $A_0$ and $B_0$). Let $q_d>0$, $\mathrm{residue}_d\colon N\to\mathbb Z$ with $|\mathrm{residue}_d(j)|\le q_d$, $C_d\equiv R_d\pmod{q_dm}$ entrywise, $\delta\ge0$ and $\sum_j|C_d(i,j)-R_d(i,j)|\le\delta H_d$ for all $d,i$. Let $\mathrm{mass}_d\colon\mathbb Z^{\mathrm{Unit}\oplus I}\to\mathbb R$, $E\ge0$, $b>0$, $r>0$, and assume that for all $d,v$, $|\mathrm{mass}_d(v)-$ `maskedIntegerImageDensity A₀ [B₀ | C d] (physicalSpatialOutputScale I (H d) (T d) L) (anisotropicSpatialKernelDensity s root M _ (H d) (T d) L …) v`$|\le E$; here `maskedIntegerImageDensity A B P f v` is the index of `pivotFullImage A B` in $\mathbb Z^{\mathrm{Unit}\oplus I}$ times $f(v_i/P_i)$ when $v$ lies in it and $0$ otherwise, the output scale is $H_d$ on the $\mathrm{Unit}$ coordinate and $LT_d$ on the others, and `anisotropicSpatialKernelDensity` is a real function on $\mathbb R^{\mathrm{Unit}\oplus I}$ (a `normalizedFiberDensity` built from $A_0,B_0$ and these scales). Let $v_d\in\mathbb Z^{\mathrm{Unit}\oplus I}$ with $|$`spatialStar (v d)`$_i/H_d|\le b$ for all $d,i$, where `spatialStar v` keeps the $\mathrm{Unit}$ coordinate $v_\ast$ and replaces $v_i$ by $v_\ast+v_i$. Put $G=m^{|\mathrm{Unit}\oplus I|}$, $f=$ `canonicalSpatialSiteDensity s root M _ W L _ _` (a real function on $\mathbb R^{\mathrm{Unit}\oplus I}$), $\mathrm{shift}_d=$ `residueMatrixShift (C d) (R d) (q d) (residue d)` $=((C_d-R_d)\,\mathrm{residue}_d)/q_d$ (integer division, coordinatewise), $\Lambda=$ `anisotropicSpatialDensityLip s κ` and $\Gamma=$ `anisotropicSpatialDensityCap s κ` (explicit real constants), and $E'=E+G\,\Lambda(1+W)\,\delta$. Then
--   $$\Big|\prod_d\mathrm{mass}_d(v_d-\mathrm{shift}_d)-\prod_d\texttt{spatialSiteApprox}\ A_0\ [B_0\,|\,\widetilde{R_d}]\ m\ f\ H_d\ b\ r\ v_d\Big|\le|D|\,(E'+4G\Lambda(1+W)\,r)\,(1+G\Gamma+E')^{|D|},$$
--   where $[X\,|\,Y]$ is `Matrix.fromCols`, $\widetilde{R_d}$ is `liftResidueMatrix (integerResidueMatrix (R d) m)` (an integer matrix with the same residues as $R_d$ modulo $m$), and `spatialSiteApprox A B m f H b r v` is a complex number (OpenAI's `maskedIntervalApprox` applied to the star-coordinate density of $f$, the mask of `pivotFullImage A B` modulo $m$, and `spatialStar v`).
--
--   Lean: `OAI.Erdos3.canonicalVectorSpatialSiteApprox_shift_error` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceWindowTest.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B089` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceWindowTest.lean#L118

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B089

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem canonicalVectorSpatialSiteApprox_shift_error {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N]
    (s : I ↪ J) (root : J → ℤ) (M : Matrix I J ℤ)
    (hpivot : (selectedSpatialPivot root M s).det ≠ 0)
    (C R : D → Matrix (Unit ⊕ I) N ℤ) (H T : D → ℝ)
    {W L κ E δ b r : ℝ} (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 < T d)
    (hW : 0 ≤ W) (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hM : ∀ i j, |(M i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (M i (s j) : ℝ) / L)).det|)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root M s) (selectedSpatialFreeColumns root M s))
    (q : D → ℕ) (hq : ∀ d, 0 < q d) (residue : D → N → ℤ)
    (hresidue : ∀ d j, |(residue d j : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix (C d) (q d * m) = integerResidueMatrix (R d) (q d * m))
    (hδ : 0 ≤ δ)
    (hmove : ∀ d i, (∑ j, |((C d i j - R d i j : ℤ) : ℝ)|) ≤ δ * H d)
    (mass : D → ((Unit ⊕ I) → ℤ) → ℝ) (hE : 0 ≤ E) (hb : 0 < b) (hr : 0 < r)
    (hmass : ∀ d v, |mass d v -
      maskedIntegerImageDensity (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d))
        (physicalSpatialOutputScale I (H d) (T d) L)
        (anisotropicSpatialKernelDensity s root M hpivot (H d) (T d) L (hH d) (hT d) hL) v| ≤ E)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    let G := (m : ℝ) ^ Fintype.card (Unit ⊕ I)
    let f := canonicalSpatialSiteDensity s root M hpivot W L hW hL
    let shift := fun d => residueMatrixShift (C d) (R d) (q d) (residue d)
    let E' := E + G * (anisotropicSpatialDensityLip s κ * (1 + W)) * δ
    ‖((∏ d, mass d (v d - shift d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (liftResidueMatrix (integerResidueMatrix (R d) m)))
        m f (H d) b r (v d)‖ ≤
      Fintype.card D * (E' + 4 * G * (anisotropicSpatialDensityLip s κ * (1 + W)) * r) *
        (1 + G * anisotropicSpatialDensityCap s κ + E') ^ Fintype.card D := by
  sorry

end Erdos3
end
end OAI
