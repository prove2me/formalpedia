-- Prove2me | Theorems.Thm_OAI_Erdos3_smoothSelectedSpatial_anisotropic_law
-- name    : OAI.Erdos3.smoothSelectedSpatial_anisotropic_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:31:58.191979+00:00
-- url     : https://prove2.me/theorems/5298b63e-9a63-43bf-a129-e9304b05deb7
-- title:
--   The smooth selected-pivot image law is the anisotropic spatial output law
-- statement:
--   Let $I,J,N$ be finite types, $\mathrm{root} : J\to\mathbb{Z}$, $D$ an $I\times J$ integer matrix, $s : I\hookrightarrow J$ an embedding, and $C$ a $(\mathrm{Unit}\oplus I)\times N$ integer matrix. Let $A,R$ be real numbers with $0<A$ and $0<R$, and $Q : N\to\mathbb{R}$ with $0<Q_j$ for every $j$. Then the following two probability mass functions on $\mathbb{Z}^{\mathrm{Unit}\oplus I}$ are equal:
--
--   - `smoothIntegerImagePMF` (OpenAI's probability mass function on $\mathbb{Z}^{\mathrm{Unit}\oplus I}$ built from a square integer matrix, a second integer matrix with the same rows, and positive scales for the columns of each) applied to the square pivot matrix `selectedSpatialPivot root D s` (the matrix `rootDifferenceMatrix` of $\mathrm{root}\circ s$ and the columns of $D$ selected by $s$), the matrix obtained by placing `selectedSpatialFreeColumns root D s` (the columns of `rootDifferenceMatrix root D` indexed by `UnselectedColumn s`, the elements of $J$ outside the range of $s$) side by side with $C$, the pivot scale `anisotropicSpatialScale I A R` (the function on $\mathrm{Unit}\oplus I$ equal to $A$ on the unit coordinate and $R$ on $I$), and the free-column scale equal to $R$ on each unselected column and to $Q$ on $N$;
--   - `anisotropicSpatialOutputLaw root D C A R Q hA hR hQ`, which is OpenAI's `smoothMatrixImagePMF` (the image under $z\mapsto Mz$ of OpenAI's smooth product law) of the matrix $M$ obtained by placing `rootDifferenceMatrix root D` (the block matrix $\begin{pmatrix}1&\mathrm{root}\\0&D\end{pmatrix}$ of shape $(\mathrm{Unit}\oplus I)\times(\mathrm{Unit}\oplus J)$) side by side with $C$, with scale `anisotropicSpatialScale J A R` on $\mathrm{Unit}\oplus J$ and $Q$ on $N$.
--
--   Lean: `OAI.Erdos3.smoothSelectedSpatial_anisotropic_law` in `lean/OAI/Combinatorics/Progressions/Probability/AnisotropicSpatialLaw.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B011` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AnisotropicSpatialLaw.lean#L44

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem smoothSelectedSpatial_anisotropic_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j) :
    smoothIntegerImagePMF (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (anisotropicSpatialScale I A R) (Sum.elim (fun _ : UnselectedColumn s => R) Q)
      (anisotropicSpatialScale_pos I hA hR) (fun j => Sum.rec (fun _ => hR) hQ j) =
      anisotropicSpatialOutputLaw root D C A R Q hA hR hQ := by
  sorry

end Erdos3
end
end OAI
