-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineL1_primitive_bounds_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:33:58.448708+00:00
-- url     : https://prove2.me/theorems/d824cf5e-641d-4b50-8788-441d3cb5e260
-- title:
--   The allocated affine L1 log budget dominates its primitive density, support, kernel, ideal-radius, Lipschitz and grid terms
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j < m$) finite types, $n : \mathrm{Fin}(m) \to \mathbb{N}$, and $B_a$ finite types indexed by the axes $a$ of `LayerSamplerAxis I n` (OpenAI's type $\Sigma_{j < m}\, (I_j \sqcup \mathrm{Fin}(n_j))$, so $a.1 = j$ is the layer of the axis $a$). Let $\alpha$ be a finite type with decidable equality and $O_j$ ($j < m$) finite types. Let $D, P, P_\rho, P_k$ be reals, and assume `AllocatedComparisonDimensions B α O D` (OpenAI's structure asserting $0 \le D$ and that $D$ bounds $m$, $|G|$, $|\alpha|$, the number of axes, and the cardinalities of several finite index types built from $B$, $\alpha$, $O$, including each $|O_j|$). Assume $P \ge 0$, $P_\rho \ge 0$, $P_k \ge 0$; let $M_k$ be a natural number with $M_k \le e^{P_k}$; let `partition` be any predicate on axes; let $R : \mathrm{Fin}(m) \to \mathbb{R}$ with $R_j \ge 0$ and $R_j^{-1} \le e^{P}$ for all $j$; and let $\rho \in \mathbb{R}_{\ge 0}$ with $\rho^{-1} \le e^{P_\rho}$.
--
--   Let $L = $ `allocatedAffineL1Log m D P Prho Pk`, a real defined by OpenAI as
--   $$P + \bigl(m 2^{m+1} P_k + \texttt{allocatedDensityEnvelope}\ m\ D\ P\bigr) + \texttt{allocatedSupportEnvelope}\ m\ D\ P + \texttt{allocatedIdealLipEnvelope}\ D\ P\ P_\rho + ((m+1) D + 2) + \texttt{scalarCubeRiemannLog}\ D,$$
--   and let $\mathrm{Output} = \Sigma_{a\,:\,\neg\mathrm{partition}(a)} O_{a.1}$. Then all of the following hold:
--   1. $0 \le L$ and $P \le L$;
--   2. `allocatedDensityLog B α O P` $\le L$ and `allocatedJetSupportLog B α O P` $\le L$ (explicit log budgets defined by OpenAI);
--   3. $\texttt{layerKernelIndexBound}\ m\ M_k \cdot \exp(\texttt{allocatedDensityLog}\ B\ \alpha\ O\ P) \le e^{L}$, where `layerKernelIndexBound m Mk` $= M_k^{m 2^{m+1}}$;
--   4. `partitionedIdealRadius α m` $+ 1 \le e^{L}$, where `partitionedIdealRadius α m` $= 1/4 + 2^{|\alpha|}(|\alpha| + 1)^m$;
--   5. $\Bigl|\bigl(\prod_{o \in \mathrm{Output}} |R_{o.1.1}|\bigr)^{-1}\Bigr| \cdot \bigl(\texttt{affineProductProfileLip Output}\ \rho \cdot e^{P}\bigr) \le e^{L}$, where the product runs over $o = (a, x)$ with factor $|R_j|$ for $j$ the first component of the axis $a$, and `affineProductProfileLip Output ρ` $= |\mathrm{Output}|\cdot$`probabilityProfileLipschitz`$\cdot \rho^{-(|\mathrm{Output}|+1)}$;
--   6. $m 2^{m+1} P_k \le L$;
--   7. `scalarCubeGridBoundaryConstant α` $/ \operatorname{vol}(\texttt{scalarCubeDomain}\ \alpha) \le e^{L}$, where `scalarCubeGridBoundaryConstant α` $= |\mathrm{Bool} \times \mathrm{Finset}\ \alpha| \cdot 4^{|\alpha|}\cdot 2\cdot(|\alpha|+1)$, `scalarCubeDomain α` is OpenAI's open subset of $\mathbb{R}^{\mathrm{Option}\ \alpha}$ of points $a$ with $a_{\mathrm{none}} + \sum_{i \in t} a_{\mathrm{some}\ i} \in (0,1)$ for all finite $t \subseteq \alpha$, and vol is Lebesgue measure (as a real number).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineScaleEnvelope.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B180` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineScaleEnvelope.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedAffineL1_primitive_bounds_s2 {D P Prho Pk : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hPrho : 0 ≤ Prho) (hPk : 0 ≤ Pk)
    {Mk : ℕ} (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (partition : LayerSamplerAxis I n → Prop)
    (R : Fin m → ℝ) (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho) :
    let L := allocatedAffineL1Log m D P Prho Pk
    let Output := Σ a : {a // ¬partition a}, O a.val.1
    0 ≤ L ∧ P ≤ L ∧
      allocatedDensityLog (G := G) B α O P ≤ L ∧
      allocatedJetSupportLog (G := G) B α O P ≤ L ∧
      (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) ≤ Real.exp L ∧
      partitionedIdealRadius α m + 1 ≤ Real.exp L ∧
      ‖(∏ o : Output, |R o.1.val.1|)⁻¹‖ *
        ((affineProductProfileLip Output ρ : ℝ) * Real.exp P) ≤ Real.exp L ∧
      ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk ≤ L ∧
      scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
