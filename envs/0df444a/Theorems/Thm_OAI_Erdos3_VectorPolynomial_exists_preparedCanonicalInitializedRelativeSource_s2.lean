-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedCanonicalInitializedRelativeSource_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedCanonicalInitializedRelativeSource_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T09:22:19.65047+00:00
-- url     : https://prove2.me/theorems/96764d16-e4bc-4774-b725-27e2a3452f51
-- title:
--   The canonical initialized relative source conclusion holds under its hypotheses
-- statement:
--   Let $n_X, m, s, D, E_{\mathrm{rest}} \in \mathbb{N}$; `prep : RankPreparationFamily (Fin nX) (Fin D) m` (a function from $\mathrm{Fin}\ m$ to OpenAI's `RankPreparationLayer`, each layer bundling finite coordinate, column and row types, rational matrices and a vector polynomial, with a `rank` and a subspace `space`); `oldPatch : PolynomialPatch (Fin nX) s (D + Erest)` (a structure bundling weights in $[1,s]$, polynomial slots of rank $D + E_{\mathrm{rest}}$ and a Lipschitz kernel with values in $[0,1]$); `F : oldPatch.LowestLayerModel m` (a structure giving a strictly lower-triangular real $D \times D$ matrix and origin polynomials of degree at most $m$ such that the first $D$ weights equal $m$ and the prefix of the patch's slots is the corresponding affine block); $\mathrm{outerDepth}, \mathrm{innerDepth}, e, C_{\mathrm{primitive}}, C_{\mathrm{direct}}, \mathrm{extra} \in \mathbb{N}$; reals $p, p_{\mathrm{Relative}}, B_{\mathrm{struct}}, \mathrm{knob}, p_{\mathrm{Prep}}, p_{\mathrm{Late}}, \mathrm{precisionBudget}$; and $R_{\mathrm{rank}} \in \mathbb{N}$. Assume, in order: `prep.PreparedHeights pPrep Rrank`; `prep.Sized D (m * D)`; $m \le s$; $1 \le s$; $0 < n_X$; $2 \le p$; $0 \le p_{\mathrm{Prep}}$; $1 \le R_{\mathrm{rank}}$; $p_{\mathrm{Prep}} \le p_{\mathrm{Late}}$; $R_{\mathrm{rank}} \le e^{p_{\mathrm{Late}}}$; `preparationCoordinateCap (max m s) D (s * D)` $\le p_{\mathrm{Late}}$; $1 \le C_{\mathrm{primitive}}$; $0 \le \mathrm{knob}$; with $M = $ `preparationCoordinateCap s D (s * D)` $= D(sD+1)^s + D + sD + 1$, $J_{\mathrm{alloc}} = $ `modularInitialBlockCount s (nX + s * M)` and $\mathrm{dim} = $ `enlargedPreparedCommonSamplerDimension s M Jalloc`, each of $p$, $s + 3$, $M$, $J_{\mathrm{alloc}}$, $\mathrm{dim}$ and `allocatedUniformChartLog M` $+ 1$ $= 20(M+1)^3 + 1$ is at most $p_{\mathrm{Relative}}$; $6p_{\mathrm{Relative}} + 35 \le B_{\mathrm{struct}}$; $3p_{\mathrm{Relative}} + 130 \le \mathrm{precisionBudget}$; $n_X \le p$; `probabilityProfileLipschitz` $\le e^{B_{\mathrm{struct}}}$ and `normalizedSiteCutoffBound` $\le e^{B_{\mathrm{struct}}}$ (fixed constants); $N : \mathrm{Fin}\ n_X \to \mathbb{N}$ with `HasLayerSamplingRank (j+1) N Rrank (prep j).space (prep j).poly` for all $j$; $e^{\rho} \le N_i$ for all $i$ and $e^{\rho} \le R_{\mathrm{rank}}$, where $\rho = $ `preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth e Cprimitive Cdirect extra Bstruct p knob` (a real budget); integer polynomials $ip_i$ ($i < D$) of total degree at most $m$, $c_0 \in \mathbb{R}^D$ and a vector polynomial $\mathrm{err}$ with `ofCoordinates` of `F.normalizedOrigin` equal to `prep.polynomial` $+$ `integerCoordinates ip` $+ (1 \otimes c_0) + \mathrm{err}$, and $|\mathrm{err}(x)_i| \le e^{-\mathrm{precisionBudget}}$ for $x \in \prod_j[0, N_j)$; naturals $n_0, \mathrm{stage}, d_0$, a real $\mathrm{discount}$ and functions $\mathrm{childCutoff}, \mathrm{childCost} : \mathbb{R} \to \mathbb{R}$ with `RelativePatchInductionRule s n₀ stage discount childCutoff childCost`; reals $a, \Lambda, \mathrm{initialCost}$ with $e^{-p} \le a \le \Lambda \le 1$ and `RelativePatchAbsoluteRule s n₀ p a Λ d₀`; `relativePatchComplexity oldPatch` $\le p$; $0 < D$; every weight of `oldPatch` beyond the first $D$ exceeds $m$; `relativePatchDistinctWeights oldPatch` (the number of distinct weights) $\le \mathrm{stage} + 1$; a function $f : \mathbb{Z}^{n_X} \to \mathbb{R}$ with $f(x) \in [0,1]$ on the box, such that `IntegerVectorAPFree {x ∈ box | f x ≠ 0} (s + 2)` (the support contains no nontrivial $(s+2)$-term arithmetic progression of integer vectors) and $e^{-p} \le$ `relativePatchBoxScore N f a oldPatch` (the box mean of $(f(x) - a)\cdot$`oldPatch.value`$(x)$); $\mathrm{discount} \in [0,1]$; $0 \le \mathrm{childCost}(p_{\mathrm{Relative}} + 2) \le \mathrm{initialCost}$; and $H, L_{\min}, Q_{\mathrm{good}} \in \mathbb{N}$ with $H \le L_{\min}$, $e^{\mathrm{childCutoff}(p_{\mathrm{Relative}}+2)} \le H \le e^{\mathrm{initialCost}}$, $L_{\min} \le e^{\mathrm{knob}}$ and $1 \le Q_{\mathrm{good}} \le e^{\mathrm{knob}}$.
--
--   Then `preparedCanonicalInitializedRelativeSourceConclusion`, applied to all of these data and hypothesis proofs, holds. That is a proposition defined by OpenAI from the canonical padded sampler data of `prep.pad (max m s)` and the budgets of the prepared finite nested schedule; it is not unfolded here.
--
--   `RelativePatchAbsoluteRule s n₀ p a Λ d₀` says: for every injective $N : \mathrm{Fin}\ n_0 \to$ primes with $N_i \le 2^{n_0+1}N_j$ and $e^p \le N_i$, and every $f$ with values in $[0,1]$ on the box, $(s+2)$-AP-free support and box mean at least $a$, `RelativePatchSliceConclusion s N f Λ d₀ p` holds. `RelativePatchInductionRule s n₀ stage τ cutoff cost` says: for all $p \ge 2$ and $e^{-p} \le a \le \Lambda \le 1$ with the absolute rule for $d_0$, every nonempty finite type $X$ with $|X| \le p$, every $N$ with $e^{\mathrm{cutoff}(p)} \le N_i$, every $f$ as above on $X$, and every polynomial patch $A$ of rank $d$ with complexity at most $p$, at most `stage` distinct weights and box score at least $e^{-p}$, `RelativePatchSliceConclusion s N f ((1-τ)^(stage+1) * Λ) (d₀ + s * d) (cost p)` holds. `RelativePatchSliceConclusion s N f target rankBound cost` asserts a residue box slice of $N$ with stride $q > 0$ and all lengths at least $e^{-\mathrm{cost}} N_i$, and a polynomial patch of rank at most $\mathrm{rankBound}$ and complexity at most $\mathrm{cost}$ whose slice score against $f - \mathrm{target}$ is at least $e^{-\mathrm{cost}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedCanonicalInitializedRelativeSource_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedCanonicalInitializedRelativeSource` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedCanonicalInitializedRelativeSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B294` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedCanonicalInitializedRelativeSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedCanonicalInitializedRelativeSource)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B294

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

theorem exists_preparedCanonicalInitializedRelativeSource_s2
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob) :
    preparedCanonicalInitializedRelativeSourceConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
