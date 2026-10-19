-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_indexed_comparable_scalar_shared_slice_tail_s2
-- name    : OAI.Erdos3.exists_indexed_comparable_scalar_shared_slice_tail_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:36:06.744519+00:00
-- url     : https://prove2.me/theorems/c7cb1837-55bc-4068-9a20-63ff3390254e
-- title:
--   Shared-slice tail bound for functions dominated by a scalar nilsequence on residue slices
-- statement:
--   Let $s, d, r$ be natural numbers with $d \ge 2$ and $r \ge 2$, and let $\varepsilon$ be a real number with $0 < \varepsilon \le 1$. Then `IndexedComparableScalarSharedSliceTailStatement s d r ε` holds. This proposition, defined by OpenAI, says the following (all named objects are OpenAI's).
--
--   There are natural numbers $A \ge 3$, $C \ge 2$ and $F \ge 2$ (the number $A$ does not appear in the rest of the statement) such that the following holds. Let $K$ be a finite type with decidable equality and $|K| = d$; let $I$ be a finite type; let $V$ be a Lie algebra over $\mathbb{Q}$ whose realification $\mathbb{R} \otimes_{\mathbb{Q}} V$ carries a Hausdorff topology making it a topological additive group with continuous real scalar multiplication; let `nilmanifold` be a `RationalFilteredNilmanifold V s d₀` (for some $d_0$). Let $p, \sigma$, level, density be reals with $2 \le p$, $|I| \le p$, $0 < \sigma \le 1$, $\sigma^{-1} \le e^p$, $e^{-p} \le \mathrm{level} \le 2$, $0 < \mathrm{density}$ and $\mathrm{density}^{-1} \le e^p$. Let $g$ be a `Niltest` on the nilmanifold with weight $1$ in each variable of $I$ satisfying `ComplexityLE p` (the nilmanifold satisfies `GeometryComplexityLE p` and $\log(2 + \text{normBound} + \text{lipBound}) \le p$); write $g(x)$ for its evaluation at $x \in \mathbb{Z}^I$. Put
--   $$\mathrm{target} = 8(rd + 1)(p+1),\qquad \mathrm{budget} = (\mathrm{target}+2)^C,\qquad \Lambda = e^{\mathrm{budget}}.$$
--   Let `parameters` $: K \to \mathbb{N}$ with $\Lambda \le \mathrm{parameters}(j) \le r\Lambda$ for all $j$. Let $\kappa$ be a nonempty finite type, `stride` $: \kappa \to \mathbb{N}$ and, for each $c \in \kappa$, $S_c$ a `ResidueBoxSlice parameters (stride c)` (start points and lengths with $\mathrm{start}_j + \mathrm{stride}(c)\,k < \mathrm{parameters}(j)$ for $k < \mathrm{length}_j$), such that $0 < \mathrm{stride}(c) \le \lceil 2/\mathrm{density}\rceil$ and $\mathrm{density}\cdot\Lambda/2 \le (S_c).\mathrm{length}(j)$ for all $c, j$. Let $N : I \to \mathbb{N}$ with $e^{(p+F)^F} \le N_i$ for all $i$, and suppose that for every $z$ in the box $\prod_i [0, N_i)$, $g(z)$ is real with $0 \le g(z) \le 1$. Put $\tau$ = `unconditionedSpatialTrimFraction |I| σ` $= \sigma/(32(|I|+1))$, $W_{\mathrm{site}} = \sum_j \mathrm{parameters}(j)$, width = `trimmedSpatialWidths W_site τ N` (a positive width function on `Option K × I`) and margin = `spatialTrimMargin τ N` $= (i \mapsto \lceil \tau N_i/4\rceil)$.
--
--   Then: every width is positive; $2\,\mathrm{margin}(i) < N_i$ for all $i$; the total selected residue smooth weight $\sum_z$ `selectedResidueSmoothWeight (fun _ => 1) {0} width z` is positive; every $(S_c).\mathrm{length}(j)$ is positive; $\mathrm{budget} \le (p+F)^F$; and for every $c \in \kappa$ and every $h : \mathbb{Z}^I \to \mathbb{C}$ with $0 \le \operatorname{Re} h(z) \le 1$ on the box, if `ResidueSliceUpperComparison h g 0 N budget level (exp (-budget))` holds (for every subbox $[\mathrm{lo}, \mathrm{lo} + N')$ of $\prod_i[0,N_i)$, every $M > 0$ and every residue $u$ such that each residue class slice has length at least $e^{-\mathrm{budget}} N_i$, the real part of the mean of $h$ over the residue class slice is at most level times that of $g$ plus $e^{-\mathrm{budget}}$), then
--   $$\Pr_{z}\Bigl[e^{-\mathrm{target}} < \mathbb{E}_{t}\Bigl(\widetilde{\operatorname{Re} h}(y_{z,t}) - (1+\varepsilon)\,\mathrm{level}\cdot \widetilde{\operatorname{Re} g}(y_{z,t})\Bigr)\Bigr] \le e^{-\mathrm{target}}.$$
--   Here $z = (z_1, z_2)$ is drawn from `selectedJointReference`: $z_1$ uniform on `trimmedIntegerBox N margin` (the box $\prod_i [\mathrm{margin}_i, N_i - \mathrm{margin}_i)$) and, independently, $z_2$ an integer array on `Option K × I` drawn with probability proportional to OpenAI's smooth product profile at $z_2/\mathrm{width}$; $t$ is uniform on $\prod_{j \in K} [0, (S_c).\mathrm{length}(j))$; $y_{z,t}$ = `smoothAffineSample` $(j \mapsto (S_c).\mathrm{start}(j) + \mathrm{stride}(c)\,t_j)$ applied to the frame `jointIntegerFrame (z₁, z₂)`, i.e. $y_{z,t}(i) = z_1(i) + z_2(\mathrm{none}, i) + \sum_{j \in K} \bigl((S_c).\mathrm{start}(j) + \mathrm{stride}(c)\,t_j\bigr)\, z_2(\mathrm{some}\ j, i)$; and $\widetilde{f}$ denotes $f$ extended by $0$ outside the box $\prod_i [0, N_i)$ (`realZeroExtendFinset`).
--
--   Lean: `OAI.Erdos3.exists_indexed_comparable_scalar_shared_slice_tail_s2`, which states OpenAI's `OAI.Erdos3.exists_indexed_comparable_scalar_shared_slice_tail` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerScalarPassage.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B248` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerScalarPassage.lean (declaration OAI.Erdos3.exists_indexed_comparable_scalar_shared_slice_tail)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248

section

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w x
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

theorem exists_indexed_comparable_scalar_shared_slice_tail_s2 (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    IndexedComparableScalarSharedSliceTailStatement.{u,v,w,x} s d r epsilon := by
  sorry

end
end Erdos3

end

end OAI
end
