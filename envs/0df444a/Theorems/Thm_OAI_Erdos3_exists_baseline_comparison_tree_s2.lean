-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_baseline_comparison_tree_s2
-- name    : OAI.Erdos3.exists_baseline_comparison_tree_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:40:01.840729+00:00
-- url     : https://prove2.me/theorems/e42d5405-05f6-4160-bca2-87542025a92f
-- title:
--   A shallow prime-coordinate tree gives stability and a refined upper comparison
-- statement:
--   For every $s \in \mathbb{N}$ there is $E \in \mathbb{N}$ with $E \ge 2$ such that the following holds. Let $\iota$ and $\sigma$ be finite types with decidable equality, let $L$ be a Lie algebra over $\mathbb{Q}$ such that $\mathbb{R} \otimes_{\mathbb{Q}} L$ carries a topology making it a Hausdorff topological additive group with continuous real scalar multiplication, let $d \in \mathbb{N}$ and `D : RationalFilteredNilmanifold L s d` (a structure bundling a nilpotent Lie filtration of $L$ of step $s$, a $\mathbb{Q}$-basis of $L$ indexed by $\mathrm{Fin}\ d$, bases of the layers, a lattice subgroup and a positive grid parameter), and let $p, \delta \in \mathbb{R}$ with $2 \le p$, $|\sigma| \le p$, $0 < \delta$ and $\delta^{-1} \le e^{p}$. Let `g : D.Niltest (fun _ : σ => 1)` (a polynomial orbit with all weights $1$ together with a bounded Lipschitz complex observable and its bounds) satisfy `g.ComplexityLE p` (the geometry of `D` has complexity at most $p$ and $\log(2 + \text{normBound} + \text{lipBound}) \le p$). Let $\mathrm{prime}, \mathrm{power} : \iota \to \mathbb{N}$ with every $\mathrm{prime}(i)$ prime, $\mathrm{prime}$ injective and $q_i := \mathrm{prime}(i)^{\mathrm{power}(i)} \le e^{p}$ for all $i$. Let $\mathrm{mandatory} \subseteq \iota$ be finite and $r \in \mathbb{N}$ with $|\mathrm{mandatory}| \le p$ and $r \le p$. Let $\mathrm{parent}, \mathrm{lo}, a : \sigma \to \mathbb{Z}$, $H, N : \sigma \to \mathbb{N}$ and $M \in \mathbb{N}$ with $0 < M$, and assume: `PhysicalSubbox parent H lo N` (for every $j$, $\mathrm{parent}_j \le \mathrm{lo}_j$ and $\mathrm{lo}_j + N_j \le \mathrm{parent}_j + H_j$); for every $z$ in `translatedIntegerBox lo N` (the box $\prod_j [\mathrm{lo}_j, \mathrm{lo}_j + N_j)$ of $\mathbb{Z}^\sigma$), `g.eval z` is real and lies in $[0,1]$; `ResidueSliceLogCostLE H lo N M a p` (for every $j$, $e^{-p} H_j$ is at most `residueIndexLength` $(\mathrm{lo}_j, \mathrm{lo}_j + N_j, M, a_j)$, the number of integers in $[\mathrm{lo}_j, \mathrm{lo}_j + N_j)$ congruent to $a_j$ mod $M$); and $e^{(p+2)^E} \le H_j$ for every $j$. Let $h : \mathbb{Z}^\sigma \to \mathbb{C}$ and $\mathrm{level}, \varepsilon \in \mathbb{R}$ with $0 \le \mathrm{level}$, and assume `ResidueSliceUpperComparison h g.eval parent H ((p + 2) ^ E) level ε` (for every $\mathrm{lo}', N', M' > 0, u$ with `PhysicalSubbox parent H lo' N'` and `ResidueSliceLogCostLE H lo' N' M' u ((p+2)^E)`, the real part of `physicalResidueMean h lo' N' M' u` is at most $\mathrm{level}$ times the real part of `physicalResidueMean g.eval lo' N' M' u` plus $\varepsilon$; `physicalResidueMean f lo N M u` is the average of $f$ over the points of the box congruent to $u$ coordinatewise mod $M$). Then there exist `tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i))` and $\mathrm{depth} \in \mathbb{N}$ with $\mathrm{depth} \le (p+2)^E$ such that `CoordinateDecisionTree.Valid Good ∅ (fun _ _ => 0) tree depth`, where `Good I x` is the conjunction of $\mathrm{mandatory} \subseteq I$, `ResiduePrimeCoordinateStable g.eval lo N M a q r δ I x` and `PrimeRefinementUpperBound h g.eval lo N M a q r level ε δ I x`.
--
--   Here `CoordinateDecisionTree ι Value` is the inductive type of trees that are a leaf or split at a coordinate $i$ with one child per value in `Value i`; `Valid Good I x tree d` holds for a leaf at any $d$ when `Good I x`, and for a split at $i \notin I$ at $d+1$ when each child for value $v$ is valid at $d$ with $I \cup \{i\}$ and $x$ updated to $v$ at $i$. For a cell `ResiduePrimeCoordinateCell lo N M a q I x` (the points of the box congruent to $a$ mod $M$ whose reduction mod $q_i$ equals $x_i$ for each $i \in I$) and the average `residuePrimeCoordinateMean` over it: `ResiduePrimeCoordinateStable f … δ I x` says that for every finite $J$ disjoint from $I$ with $|J| \le r$ and every $y$ agreeing with $x$ on $I$ whose $(I \cup J, y)$-cell is nonempty, the means of $f$ over the $(I,x)$-cell and the $(I\cup J, y)$-cell differ in norm by at most $\delta$; `PrimeRefinementUpperBound h g … level ε δ I x` says that for the same $J, y$, the real part of the mean of $h$ over the $(I\cup J, y)$-cell is at most $\mathrm{level}$ times the real part of the mean of $g$ over the $(I,x)$-cell, plus $\varepsilon + \mathrm{level}\cdot\delta$. `g.eval z` is the observable evaluated at the image of the polynomial orbit at $z$.
--
--   Lean: `OAI.Erdos3.exists_baseline_comparison_tree_s2`, which states OpenAI's `OAI.Erdos3.exists_baseline_comparison_tree` (in `lean/OAI/Combinatorics/Progressions/Estimates/BaselineNoIncrementTree.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B092`, `OAIE3v2B097`, `OAIE3v2B101` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/BaselineNoIncrementTree.lean (declaration OAI.Erdos3.exists_baseline_comparison_tree)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B097
import Definitions.Def_OAIE3v2B101

section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u v w

theorem exists_baseline_comparison_tree_s2 (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ g : D.Niltest (fun _ : σ => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (parent : σ → ℤ) (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M →
    PhysicalSubbox parent H lo N →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N M a p →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∀ (h : (σ → ℤ) → ℂ) (level ε : ℝ), 0 ≤ level →
    ResidueSliceUpperComparison h g.eval parent H ((p + 2) ^ E) level ε →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable g.eval lo N M a (fun i => prime i ^ power i) r δ I x ∧
          PrimeRefinementUpperBound h g.eval lo N M a (fun i => prime i ^ power i) r level ε δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  sorry

end Erdos3

end

end OAI
end
