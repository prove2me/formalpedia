-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_3_7
-- name    : GaussPolyReg.Approx.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:52.709505+00:00
-- url     : https://prove2.me/theorems/1204c359-2ce1-4d3e-a0c9-475084e77f22
-- title:
--   Lemma 3.7 — top products of primitives equal normalized Hermites
-- statement:
--   Let $e_i=[e_{n,i}]$ be an arbitrary orthonormal basis in each positive-degree primitive space, with grade $g_i$ and representatives normalized along $U$. For every finitely supported $\alpha:I\to\mathbb N$,
--
--   $$\frac1{\sqrt{\alpha!}}\mathop{\diamond}_{i\in I} e_i^{\diamond\alpha_i}=[\psi_\alpha(e_n)].$$
--
--   Equality is expressed as the squared L² error tending to zero along $U$, using the lower integral of the raw Hermite composition. No class of an unverified L² function is formed. This is the identification of the top-product and ordinary Hermite constructions.
--
--   Differences from the source:
--   - encoding: equality of classes in the homogeneous ultraproduct → bounded homogeneous representatives and equality expressed by lower-integral squared error tending to zero along U; reason: the squared-error nullspace is exactly N_d; the definitions do not assume the asserted class equality
--   - reading: I is written as the disjoint union of I_d over natural d, while §2 requires strictly positive grades → an arbitrary index set graded by positive natural numbers, with each grade fiber a primitive basis; reason: including grade zero would admit e=±1 and ψ₂(e)=0, contradicting orthonormality; follows the standing convention in §2
--   - generalization: representatives normalized to E e²_{n,i}=1 exactly → normalization for U-almost every n; reason: the stronger source hypothesis implies this one; n=0 has no nonzero positive-degree chaos, and changing U-small sets changes no class
--   - encoding: equality of the iterated top-product class and the Hermite-composition class → one projection of the ordinary power product, scaled by 1/√α!, and convergence of its lower-integral squared error to zero; reason: the final top-degree projection equals the iterated top product; a lower integral prevents spurious zero error
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma 3.7, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Ultra

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem lemma_3_7 {I : Type*} (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite) (g : I → ℕ) (e : I → Sequence)
    (he : PrimitiveBasis U g e) (α : I →₀ ℕ) :
    Tendsto (fun n => ∫⁻ x,
      ENNReal.ofReal ((topMulti g e α n x - psiSequence e α n x) ^ 2)
        ∂gaussianProduct ℕ) (U : Filter ℕ) (𝓝 0) := by sorry

end GaussPolyReg.Approx
