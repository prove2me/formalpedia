-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_coprime_residue_physical_stability_s2
-- name    : OAI.Erdos3.exists_coprime_residue_physical_stability_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:42:12.763559+00:00
-- url     : https://prove2.me/theorems/4754a6d6-1366-4f9a-8774-5417d3150748
-- title:
--   A niltest's residue-cell averages become stable after querying polynomially many prime-power coordinates
-- statement:
--   Let $s$ be a natural number. Then there is a natural number $E \ge 2$ with the following property.
--
--   Let $\iota$, $\sigma$, $L$ be types (in arbitrary universes) with $\iota$ and $\sigma$ finite with decidable equality, and $L$ a Lie algebra over $\mathbb{Q}$ such that $\mathbb{R} \otimes_{\mathbb{Q}} L$ carries a Hausdorff topology making it a topological additive group with continuous real scalar multiplication. Let $d$ be a natural number and $D$ a rational filtered nilmanifold (OpenAI's `RationalFilteredNilmanifold L s d`). Let $p, \delta$ be reals with $p \ge 2$, $|\sigma| \le p$, $\delta > 0$ and $\delta^{-1} \le e^{p}$. Let $T$ be a niltest on $D$ in the variables $\sigma$, each of weight $1$ (OpenAI's `D.Niltest (fun _ => 1)`), whose observable takes values in $[0,1]$ (`T.UnitIntervalValued`) and whose complexity is at most $p$ (`T.ComplexityLE p`); write $T.\mathrm{eval} : \mathbb{Z}^{\sigma} \to \mathbb{C}$ for its evaluation. Let `prime, power : ι → ℕ` with every $\mathrm{prime}_i$ prime, `prime` injective, and $q_i := \mathrm{prime}_i^{\mathrm{power}_i} \le e^{p}$ for all $i$. Let `mandatory` $\subseteq \iota$ be a finite set and $r$ a natural number with $|\mathrm{mandatory}| \le p$ and $r \le p$. Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$, $a : \sigma \to \mathbb{Z}$ with $0 < M \le e^{p}$, $M$ coprime to every $q_i$, and $e^{(p+2)^E} \le N_j$ for every $j \in \sigma$.
--
--   Then there are a coordinate decision tree `tree` (OpenAI's `CoordinateDecisionTree ι (fun i => σ → ZMod (q i))`: either a leaf, or a node that queries a coordinate $i$ and branches on its value, a residue array $\sigma \to \mathbb{Z}/q_i$) and a natural number `depth` with $\mathrm{depth} \le (p+2)^E$, such that `CoordinateDecisionTree.Valid Good ∅ (fun _ _ => 0) tree depth` holds. Here `Valid Good I x tree d` is defined inductively by OpenAI: a leaf is valid at $(I, x, d)$ iff $\mathrm{Good}(I, x)$; a node querying $i$ is valid at $(I, x, d+1)$ iff $i \notin I$ and every child, for every value $v$, is valid at $(I \cup \{i\},\ x[i \mapsto v],\ d)$. And $\mathrm{Good}(I, x)$ means: $\mathrm{mandatory} \subseteq I$ and `ResiduePrimeCoordinateStable T.eval lo N M a q r δ I x`, i.e. for every finite $J \subseteq \iota$ disjoint from $I$ with $|J| \le r$ and every $y$ agreeing with $x$ on $I$ such that the cell for $(I \cup J, y)$ is nonempty,
--   $$\bigl\| \mu(I, x) - \mu(I \cup J, y) \bigr\| \le \delta,$$
--   where $\mu(I, x)$ = `residuePrimeCoordinateMean T.eval lo N M a q I x` is the average of $T.\mathrm{eval}$ over the cell of integer arrays $z$ with $z_j \in [\mathrm{lo}_j, \mathrm{lo}_j + N_j)$, $z_j \equiv a_j \pmod M$ for all $j$, and $z \bmod q_i = x_i$ for all $i \in I$.
--
--   Lean: `OAI.Erdos3.exists_coprime_residue_physical_stability_s2`, which states OpenAI's `OAI.Erdos3.exists_coprime_residue_physical_stability` (in `lean/OAI/Combinatorics/Progressions/Lattices/CoprimeResiduePhysicalStability.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B097`, `OAIE3v2B115` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/CoprimeResiduePhysicalStability.lean (declaration OAI.Erdos3.exists_coprime_residue_physical_stability)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B097
import Definitions.Def_OAIE3v2B115

section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_coprime_residue_physical_stability_s2 (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ), 0 < M → (M : ℝ) ≤ Real.exp p →
    (∀ i, M.Coprime (prime i ^ power i)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (N j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  sorry

end Erdos3

end

end OAI
end
