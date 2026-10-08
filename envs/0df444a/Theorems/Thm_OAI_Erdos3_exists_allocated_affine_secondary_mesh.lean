-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_allocated_affine_secondary_mesh
-- name    : OAI.Erdos3.exists_allocated_affine_secondary_mesh
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:41:04.594784+00:00
-- url     : https://prove2.me/theorems/b04feee4-3560-4315-9e78-0ac467f2a66f
-- title:
--   Existence of source and parameter meshes that rarely straddle a physical cell boundary
-- statement:
--   Let $J,I$ be finite types with decidable equality. Let $\mathrm{sourceLo},\mathrm{sourceHi}\colon\mathrm{Option}\,J\times I\to\mathbb Z$ with $\mathrm{sourceLo}(z)<\mathrm{sourceHi}(z)$; $\mathrm{parLo},\mathrm{parHi},\mathrm{anchor}\colon J\to\mathbb Z$ with $\mathrm{parLo}_j<\mathrm{parHi}_j$; $D\in\mathbb N$ with $D>0$; $\mathrm{lo}\colon I\to\mathbb Z$, $N\colon I\to\mathbb N$, $H\colon I\to\mathbb R$; and reals $L,C,B,A,c,\rho,\mathrm{sourceRatio},\mathrm{parameterRatio},U,\mathrm{lengthLog},\beta$. Assume: $L>0$; $H_i>0$; $C,B,A\ge0$; $c>0$; $\rho>0$; $\mathrm{sourceRatio},\mathrm{parameterRatio},U,\mathrm{lengthLog}\ge0$; $\beta>0$; $4\le\rho H_i\le 2N_i$ and $N_i\le AH_i$ for all $i$; $cH_i\le\mathrm{sourceHi}(\mathrm{none},i)-\mathrm{sourceLo}(\mathrm{none},i)$ for all $i$; $|(\mathrm{anchor}_j+D\,\mathrm{parLo}_j)/L|\le C$ and $|(\mathrm{anchor}_j+D\,\mathrm{parHi}_j)/L|\le C$ for all $j$; $|\mathrm{sourceLo}(\mathrm{some}\ j,i)|\le BH_i/L$ and $|\mathrm{sourceHi}(\mathrm{some}\ j,i)|\le BH_i/L$ for all $j,i$; $40|I|A/(\rho c)\le e^U$, $1+|J|(C+B)\le e^U$, $\mathrm{sourceRatio}\le e^U$, $\mathrm{parameterRatio}\le e^U$ and $\beta^{-1}\le e^U$; for every $z=(o,i)$, $\sigma(z)\le\mathrm{sourceRatio}\cdot\mathrm{toNat}(\mathrm{sourceHi}(z)-\mathrm{sourceLo}(z))$ and $4e^{4U+18+\mathrm{lengthLog}}\le\sigma(z)$, where $\sigma(o,i)=$ `smoothPairCoefficientScale (H i) L o` ($H_i$ for $o=\mathrm{none}$, $H_i/L$ otherwise); and for every $j$, $L/D\le\mathrm{parameterRatio}\cdot\mathrm{toNat}(\mathrm{parHi}_j-\mathrm{parLo}_j)$, together with $4e^{4U+18+\mathrm{lengthLog}}\le L/D$. Let $P=$ `normalizedBoxPartitions N H ρ …`. Then there exist, for each $z$, a `FiniteProgressionPartition` $S_z$ of $\mathrm{toNat}(\mathrm{sourceHi}(z)-\mathrm{sourceLo}(z))$ and, for each $j$, a `FiniteProgressionPartition` $T_j$ of $\mathrm{toNat}(\mathrm{parHi}_j-\mathrm{parLo}_j)$, all of whose blocks have step $1$ and length at least $e^{\mathrm{lengthLog}}$ (in particular positive), such that the following event has probability at most $\beta$ when $t\in\prod_j\{\mathrm{parLo}_j,\dots,\mathrm{parHi}_j-1\}$ and $w\in\prod_z\{\mathrm{sourceLo}(z),\dots,\mathrm{sourceHi}(z)-1\}$ are independent and uniform (`integerBoxUniformWeights`, combined by `prod`): `physicalMeshCrossing lo N P mesh location (t, w)`, which says that some $(t',w')$ with the same mesh value has location classified differently by `physicalBoxClassify lo N P` (the cell of the product partition $P$ containing the point, or `none` outside the box $\mathrm{lo}_i\le x_i<\mathrm{lo}_i+N_i$). Here the mesh value of $(t,w)$ is the pair of the cell of $w$ in the product of the $S_z$ and the cell of $t$ in the product of the $T_j$ (`integerBoxMesh`), and the location is `smoothAffineSample` $(j\mapsto\mathrm{anchor}_j+Dt_j)$ $w$, the point $i\mapsto w(\mathrm{none},i)+\sum_j(\mathrm{anchor}_j+Dt_j)\,w(\mathrm{some}\ j,i)$ of $\mathbb Z^I$. Throughout, $\mathrm{toNat}$ truncates an integer at $0$.
--
--   Lean: `OAI.Erdos3.exists_allocated_affine_secondary_mesh` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineSecondaryMesh.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B016` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineSecondaryMesh.lean#L12

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem exists_allocated_affine_secondary_mesh {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
    (parLo parHi anchor : J → ℤ) (hpar : ∀ j, parLo j < parHi j) (D : ℕ) (hD : 0 < D)
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) {L C B A c rho sourceRatio parameterRatio U lengthLog beta : ℝ}
    (hL : 0 < L) (hH : ∀ i, 0 < H i) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hc : 0 < c) (hrho : 0 < rho) (hsRatio : 0 ≤ sourceRatio) (hpRatio : 0 ≤ parameterRatio)
    (hU : 0 ≤ U) (hlength : 0 ≤ lengthLog) (hbeta : 0 < beta)
    (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hsiteRatio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hbaseWidth : ∀ i, c * H i ≤ ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ))
    (hparamLo : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hparamHi : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hsourceLo : ∀ j i, |(sourceLo (some j, i) : ℝ)| ≤ B * H i / L)
    (hsourceHi : ∀ j i, |(sourceHi (some j, i) : ℝ)| ≤ B * H i / L)
    (hboundaryU : 40 * (Fintype.card I : ℝ) * A / (rho * c) ≤ Real.exp U)
    (hmovementU : 1 + (Fintype.card J : ℝ) * (C + B) ≤ Real.exp U)
    (hsourceU : sourceRatio ≤ Real.exp U) (hparameterU : parameterRatio ≤ Real.exp U)
    (hbetaU : beta⁻¹ ≤ Real.exp U)
    (hsourceWidth : ∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      sourceRatio * ((sourceHi z - sourceLo z).toNat : ℝ))
    (hparameterWidth : ∀ j, L / (D : ℝ) ≤ parameterRatio * ((parHi j - parLo j).toNat : ℝ))
    (hsourceScale : ∀ z : Option J × I, 4 * Real.exp (4 * U + 18 + lengthLog) ≤
      smoothPairCoefficientScale (H z.2) L z.1)
    (hparameterScale : 4 * Real.exp (4 * U + 18 + lengthLog) ≤ L / (D : ℝ)) :
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    ∃ (S : ∀ z, FiniteProgressionPartition (sourceHi z - sourceLo z).toNat)
      (T : ∀ j, FiniteProgressionPartition (parHi j - parLo j).toNat),
    (∀ z cs, (S z).step cs = 1) ∧ (∀ z cs, 0 < (S z).length cs) ∧
    (∀ j ct, (T j).step ct = 1) ∧ (∀ j ct, 0 < (T j).length ct) ∧
    (∀ z cs, Real.exp lengthLog ≤ ((S z).length cs : ℝ)) ∧
    (∀ j ct, Real.exp lengthLog ≤ ((T j).length ct : ℝ)) ∧
    ((integerBoxUniformWeights parLo parHi hpar).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh parLo parHi T tz.1))
        (fun tz => smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val)
          (fun i => (tz.2 i).val))) ≤ beta := by
  sorry

end Erdos3
end
end OAI
