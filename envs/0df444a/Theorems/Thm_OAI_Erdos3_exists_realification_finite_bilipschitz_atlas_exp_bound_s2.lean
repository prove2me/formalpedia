-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_realification_finite_bilipschitz_atlas_exp_bound_s2
-- name    : OAI.Erdos3.exists_realification_finite_bilipschitz_atlas_exp_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:31:40.124821+00:00
-- url     : https://prove2.me/theorems/0bfab0c5-00c1-4689-9b8c-7a6efd66b486
-- title:
--   A finite bi-Lipschitz atlas with quantitative bounds for the realified nilmanifold quotient
-- statement:
--   For every natural number $s$ there is a natural number $D \ge 2$ with the following property.
--
--   Let $\iota$ be a finite type and $L$ a Lie algebra over $\mathbb{Q}$, with the topological-vector-space instances (topological additive group, continuous scalar multiplication, Hausdorff) on $\mathbb{R} \otimes_{\mathbb{Q}} L$. Let $e$ be a $\mathbb{Q}$-basis of $L$ indexed by $\iota$, and assume the $s$-th term of the lower central series of $L$ is zero. Let $\Gamma$ be a subgroup of `NilpotentLieBCHGroup L s hnil` (OpenAI: $L$ with the Baker–Campbell–Hausdorff group law). Let $l, H$ be natural numbers and $p$ a real number with $l > 0$, and assume the coordinates of $\Gamma$ in the basis $e$ are sandwiched between grids: `scaledIntegerGrid l` $\subseteq$ `bchSubgroupCoordinates e Γ` $\subseteq$ `denominatorGrid l` (OpenAI's grids of mesh related to $l$; the first is the set of integer vectors scaled by $l$, the second the set of vectors with denominators dividing $l$). Assume every structure constant of $L$ in the basis $e$ is a rational number of height at most $H$ (`RationalHeightLE`), $0 \le p$, $\lvert\iota\rvert \le p$, $H \le e^p$ and $l \le e^p$.
--
--   Let $G$ be the BCH group of the realification $\mathbb{R} \otimes_{\mathbb{Q}} L$ (step $s$), $\Gamma_{\mathbb{R}}$ the image of $\Gamma$ under the realification homomorphism, and equip $G/\Gamma_{\mathbb{R}}$ with OpenAI's metric `realificationQuotientMetricSpace e Γ l hl houter`. Write $Q = e^{(p + D)^D}$. Then there exist:
--   - a real $r$ with $0 < r \le 1$ and $1/r \le Q$;
--   - $K \in \mathbb{R}_{\ge 0}$ with $K \le Q$;
--   - a natural number $n$ with $0 < n \le Q$;
--   - centers $c_1, \dots, c_n \in G$ and open partial homeomorphisms $\varphi_1, \dots, \varphi_n$ from $\mathbb{R}^\iota$ to $G/\Gamma_{\mathbb{R}}$,
--
--   such that: every coordinate of every center $c_j$ in the base-changed basis $e \otimes \mathbb{R}$ has absolute value at most $Q$; $\varphi_j(v)$ is the coset of $c_j \cdot \Phi^{-1}(v)$, where $\Phi$ is OpenAI's coordinate homeomorphism `basisHomeomorph (e.baseChange ℝ)` of $G$ with $\mathbb{R}^\iota$; the source of each $\varphi_j$ is the open cube $\{v : \lvert v_i\rvert < r \text{ for all } i\}$; each $\varphi_j$ is $K$-Lipschitz on its source and its inverse is $K$-Lipschitz on its target; and every point $x \in G/\Gamma_{\mathbb{R}}$ equals $\varphi_j(u)$ for some $j$ and some $u$ with $\lvert u_i\rvert \le r/2$ for all $i$.
--
--   Lean: `OAI.Erdos3.exists_realification_finite_bilipschitz_atlas_exp_bound_s2`, which states OpenAI's `OAI.Erdos3.exists_realification_finite_bilipschitz_atlas_exp_bound` (in `lean/OAI/Combinatorics/Progressions/Nilpotent/RealifiedBCHSmoothPartition.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B068` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Nilpotent/RealifiedBCHSmoothPartition.lean (declaration OAI.Erdos3.exists_realification_finite_bilipschitz_atlas_exp_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068

section

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_finite_bilipschitz_atlas_exp_bound_s2 (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (_hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ centers : Fin n → G, ∃ φ : Fin n → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ j i, |(e.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + D) ^ D)) ∧
          (∀ j v, φ j v = (QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ j, (φ j).source = {v | ∀ i, |v i| < r}) ∧
          (∀ j, LipschitzOnWith K (φ j) (φ j).source) ∧
          (∀ j, LipschitzOnWith K (φ j).symm (φ j).target) ∧
          (∀ x : G ⧸ ΓR, ∃ j, ∃ u : ι → ℝ, (∀ i, |u i| ≤ r / 2) ∧ φ j u = x) := by
  sorry

end Erdos3

end

end OAI
end
