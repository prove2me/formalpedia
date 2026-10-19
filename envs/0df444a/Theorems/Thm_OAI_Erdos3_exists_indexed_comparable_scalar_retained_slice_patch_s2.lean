-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_indexed_comparable_scalar_retained_slice_patch_s2
-- name    : OAI.Erdos3.exists_indexed_comparable_scalar_retained_slice_patch_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:08:26.32099+00:00
-- url     : https://prove2.me/theorems/f9f467fe-b64c-4357-9a1e-b0d1bbcebaa7
-- title:
--   Many retained frames with a correlating residue slice give a relative patch slice
-- statement:
--   Let $s, d, r \in \mathbb{N}$ with $2 \le d$ and $2 \le r$, and let $\tau \in \mathbb{R}$ with $0 < \tau \le 1/2$. Then there are $C, F \in \mathbb{N}$ with $2 \le C$ and $2 \le F$ such that the following holds. Let $K$ be a finite type with decidable equality and $|K| = d$; let $I$ be a finite type; let $V$ be a Lie algebra over $\mathbb{Q}$ such that $\mathbb{R} \otimes_{\mathbb{Q}} V$ carries a topology making it a Hausdorff topological additive group with continuous real scalar multiplication; let $d_0, \mathrm{rank} \in \mathbb{N}$ and `nilmanifold : RationalFilteredNilmanifold V s d₀` (a structure bundling a nilpotent Lie filtration of step $s$, a $\mathbb{Q}$-basis indexed by $\mathrm{Fin}\ d_0$, layer bases, a lattice subgroup and a positive grid parameter); and let $p, \sigma, \Lambda, \mathrm{density}, \mathrm{accuracy}, \mathrm{gain} \in \mathbb{R}$ with $2 \le p$, $|I| \le p$, $0 < \sigma \le 1$, $\sigma^{-1} \le e^{p}$, $\Lambda \in [0,1]$, $e^{-p} \le (1-\tau)\Lambda$, $0 < \mathrm{density} \le 1$, $\mathrm{density}^{-1} \le e^{p}$ and $0 < \mathrm{accuracy} \le 1$. Let `P : PolynomialPatch I s rank` (a structure bundling weights in $[1,s]$, polynomial slots on $\mathbb{R}^I$ of rank $\mathrm{rank}$ and a Lipschitz kernel with values in $[0,1]$; `P.value` is the resulting real function on $\mathbb{R}^I$) and `g : nilmanifold.Niltest (fun _ : I => 1)` (a polynomial orbit with all weights $1$ and a bounded Lipschitz complex observable) with `g.ComplexityLE p`, `relativePatchComplexity P` $\le p$ (this is $\mathrm{rank} + \log(1 + \text{kernel Lipschitz constant})$), and `g.eval x` $=$ `P.value x` for every $x \in \mathbb{Z}^I$. Put $\mathrm{target} = 8(rd + 1)(p+1)$, $\mathrm{budget} = (\mathrm{target} + 2)^C$, $L = e^{\mathrm{budget}}$, $Q = \lceil 2/\mathrm{density} \rceil$ and $\mathrm{meshCap} = $ `denseResidueMeshCap d density accuracy r` $= \lceil 16(d+1)r/(\mathrm{accuracy}\cdot\mathrm{density}) \rceil + 1$. Assume $e^{-\mathrm{target}} < \mathrm{gain} - \mathrm{accuracy}/2$ and $16(d+1)/(\mathrm{accuracy}\cdot\mathrm{density}) \le L$. Let $\mathrm{parameters} : K \to \mathbb{N}$ with $L \le \mathrm{parameters}_j \le rL$ for all $j$, let $N : I \to \mathbb{N}$ with $e^{(p+F)^F} \le N_i$ for all $i$, and let $f : \mathbb{Z}^I \to \mathbb{R}$ with $f(x) \in [0,1]$ for every $x$ in the box $B = \prod_i [0, N_i)$. Put $\mathrm{trim} = $ `unconditionedSpatialTrimFraction |I| σ` $= \sigma/(32(|I|+1))$, $W = \sum_j \mathrm{parameters}_j$, `width := trimmedSpatialWidths W trim N` (positive-real widths indexed by $\mathrm{Option}\ K \times I$) and `margin := spatialTrimMargin trim N` ($i \mapsto \lceil \mathrm{trim}\cdot N_i/4\rceil$). Then there exist proofs that every width is positive, that $2\,\mathrm{margin}_i < N_i$ for all $i$ and that $\sum'_z$ `selectedResidueSmoothWeight (fun _ => 1) {0} width z` $> 0$, such that, writing `outer` for the law `selectedJointReference` (the product of the uniform law on `trimmedIntegerBox N margin` $= \prod_i [\mathrm{margin}_i, N_i - \mathrm{margin}_i)$ with OpenAI's smooth-weighted law on frame offsets in `rectangularWeightIndices 0 width 1`), the following holds for every predicate `retained` on samples $z = (z_1, z_2)$ of `outer`. Assume (1) $|$`DenseResidueSliceNetCode K Q meshCap`$|\cdot e^{-\mathrm{target}}$ is less than the `outer`-probability of `retained` (that type is $\mathrm{Fin}(Q+1) \times (K \to \mathrm{Fin}(Q+1)) \times (K \to \mathrm{Fin}(\mathrm{meshCap}+1))^2$); (2) for every retained $z$ and every $u$ in $\prod_j [0, \mathrm{parameters}_j)$, the point $x_u(z) := $ `smoothAffineSample u (jointIntegerFrame (z.1, z.2))` $= z_1 + z_2(\mathrm{none},\cdot) + \sum_k u_k\, z_2(\mathrm{some}\ k, \cdot)$ lies in $B$; and (3) for every retained $z$ there are $q > 0$ and `S : ResidueBoxSlice parameters q` (a start and a length per $j$ with $\mathrm{start}_j + q\,i < \mathrm{parameters}_j$ for $i < \mathrm{length}_j$) with all lengths positive, $\mathrm{density}\cdot\mathrm{parameters}_j \le \mathrm{length}_j$ for all $j$, and
--   $$\mathrm{gain} \le \mathbb{E}_{u}\big[(f(x_u(z)) - \Lambda)\, P.\mathrm{value}(x_u(z))\big],$$
--   the mean over $u$ taken under `S.fullSliceLaw` (the image of the uniform law on $\prod_j [0, \mathrm{length}_j)$ under $i \mapsto (\mathrm{start}_j + q\, i_j)_j$). Then `RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F)` holds: there are $q' > 0$, `S' : ResidueBoxSlice N q'`, $d' \le \mathrm{rank}$ and `A : PolynomialPatch I s d'` with $e^{-(p+F)^F} N_i \le \mathrm{length}'_i$ for all $i$, `relativePatchComplexity A` $\le (p+F)^F$, and $e^{-(p+F)^F} \le$ `relativePatchSliceScore S' f ((1 - τ) * Λ) A`, the mean over $x \in \prod_i [0, \mathrm{length}'_i)$ of $(f(\mathrm{start}' + q' x) - (1-\tau)\Lambda)\cdot A.\mathrm{value}(x)$.
--
--   Lean: `OAI.Erdos3.exists_indexed_comparable_scalar_retained_slice_patch_s2`, which states OpenAI's `OAI.Erdos3.exists_indexed_comparable_scalar_retained_slice_patch` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerScalarPassage.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B117`, `OAIE3v2B151` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerScalarPassage.lean (declaration OAI.Erdos3.exists_indexed_comparable_scalar_retained_slice_patch)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B151

section

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  Fintype.card

theorem exists_indexed_comparable_scalar_retained_slice_patch_s2 (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ C F : ℕ, 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {p σ Λ density accuracy gain : ℝ},
    2 ≤ p → (Fintype.card I : ℝ) ≤ p →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-p) ≤ (1 - τ) * Λ →
    0 < density → density ≤ 1 → density⁻¹ ≤ Real.exp p →
    0 < accuracy → accuracy ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE p → relativePatchComplexity P ≤ p →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    let Q := ⌈2 / density⌉₊
    let meshCap := denseResidueMeshCap d density accuracy (r : ℝ)
    Real.exp (-target) < gain - accuracy / 2 →
    16 * ((d : ℝ) + 1) / (accuracy * density) ≤ L →
    ∀ parameters : K → ℕ,
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ retained : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card (DenseResidueSliceNetCode K Q meshCap) : ℝ) * Real.exp (-target) <
        outer.eventProbability retained →
      (∀ z, retained z → ∀ u : integerBox parameters,
        smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) ∈
          translatedIntegerBox (0 : I → ℤ) N) →
      (∀ z, retained z → ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        gain ≤ (S.fullSliceLaw hlen).mean (fun u =>
          (f (smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) - Λ) *
            P.value (fun i => (smoothAffineSample u.val
              (fun k => jointIntegerFrame (z.1.val,z.2.val) k.1 k.2) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  sorry

end
end Erdos3

end

end OAI
end
