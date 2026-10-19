-- Prove2me | Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_physicalRowChart_base_matching_s2
-- name    : OAI.Erdos3.BooleanCubeKernel.physicalRowChart_base_matching_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:26:42.120751+00:00
-- url     : https://prove2.me/theorems/1990bdd7-8bf5-4950-9cbb-fa6a7bbd7385
-- title:
--   A mixed covered jet chart matching the physical cube row sample recovers each physical site point modulo the integer lattice
-- statement:
--   Let $X$ be a type, $m, \mathrm{dim}$ natural numbers, and for each $j \in \operatorname{Fin} m$ let $I_j, J_j, E_j$ be finite types and $n_j$ a natural number. For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be the same subspace viewed inside the Euclidean space $\mathbb{R}^{J_j}$ (defined by OpenAI), let $o_j$ be an orthonormal basis, indexed by $I_j$, of `euclideanSubspace (U j)`, let $b_j$ be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement, such that the integer span of $b_j$ equals `projectedIntegerLattice` (the orthogonal projection of the standard lattice $\mathbb{Z}^{J_j}$ onto that orthogonal complement, defined by OpenAI), and let $bW_j$ be a $\mathbb{Z}$-basis, indexed by $E_j$, of `latticeSection` (the intersection of $\mathbb{Z}^{J_j}$ with `euclideanSubspace (U j)`, as a lattice in that subspace; defined by OpenAI). Let $d \ne 0$ be a natural number. For $j \in \operatorname{Fin} m$ let $\mathrm{rowSets}_j$ = `boundedBooleanJetRows (Fin dim) (j+1)`, the set of subsets of $\operatorname{Fin} \mathrm{dim}$ of size at most $j+1$, and let $O_j$ be the type of elements of $\mathrm{rowSets}_j$.
--
--   Let $p_j$, for $j \in \operatorname{Fin} m$, be vector-valued polynomials in the variables $X$ with real coefficients in $J_j \to \mathbb{R}$ (`VectorPolynomial X ℝ (J j → ℝ)`, i.e. $\mathbb{R}[X] \otimes (J_j \to \mathbb{R})$), such that each $p_j$ has total degree at most $j+1$ (every coefficient of a monomial of total degree greater than $j+1$ is zero) and every coefficient of $p_j$ lies in $U_j$ (hypothesis $hm$). Let $v : X \to (\mathrm{Unit} \sqcup \operatorname{Fin} \mathrm{dim}) \to \mathbb{Z}$, and let $z$ be an element of `MixedCoveredJetSource I O E n d` (for each $j$: a pair of a real array $I_j \to O_j \to \mathbb{R}$ and an integer array $\operatorname{Fin} n_j \to O_j \to \mathbb{Z}$, together with, for each $j$, an array $O_j \to E_j \to \mathbb{Z}/d$). Assume that
--   `mixedCoveredJetChart U o b hb bW d z` $=$ `physicalCubeRowSample U d (fun _ => Subtype.val) p hm v`,
--   where `mixedCoveredJetChart` is OpenAI's chart from such sources to jet layers, and `physicalCubeRowSample` is OpenAI's jet-layer sample of the polynomials $p$ at the integer cube vertices determined by $v$, with each row index $t \in O_j$ read as its underlying subset of $\operatorname{Fin} \mathrm{dim}$.
--
--   Then for every finite set $s \subseteq \operatorname{Fin} \mathrm{dim}$ and every $j \in \operatorname{Fin} m$ the following holds. Let $w : X \to \mathbb{R}$ be the cube vertex $w(x) = v(x, \ast) + \sum_{a \in s} v(x, a)$ (`physicalCubeVertexValue v s`, cast to $\mathbb{R}$), and let `physicalEuclideanSitePoint U p hm w j` be the evaluation of $p_j$ at $w$, as a point of `euclideanSubspace (U j)` (defined by OpenAI). Then the class of this point in the quotient of `euclideanSubspace (U j)` by the lattice `latticeSection` of $\mathbb{Z}^{J_j}$ equals
--   `normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) c`,
--   where $c$ is the pair (a point of `euclideanSubspace (U j)`, an integer vector in $\mathbb{Z}^{n_j}$) given by the first component of `mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()`. Here `mixedCoveredRowsSiteValue rowSets d z s` is OpenAI's single-site source obtained from $z$ by the row-restricted site matrix of $s$, `mixedCoveredJetCoordinates` converts real arrays to points of the subspaces using the orthonormal bases $o_j$, and `normalizedLatticeQuotient` sends a pair $(x, k)$ to the class of $x - \sigma(k)$, where $\sigma(k) \in$ `euclideanSubspace (U j)` is a shift determined by the lattice point $\sum_i k_i b_{j,i}$ of `projectedIntegerLattice` (all defined by OpenAI).
--
--   Lean: `OAI.Erdos3.BooleanCubeKernel.physicalRowChart_base_matching_s2`, which states OpenAI's `OAI.Erdos3.BooleanCubeKernel.physicalRowChart_base_matching` (in `lean/OAI/Combinatorics/Progressions/Geometry/PhysicalRowChartMatching.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B161`, `OAIE3v2B162` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PhysicalRowChartMatching.lean (declaration OAI.Erdos3.BooleanCubeKernel.physicalRowChart_base_matching)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162

section

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule VectorPolynomial
open scoped Classical

variable {X : Type*} {m dim : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

theorem physicalRowChart_base_matching_s2
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (z : MixedCoveredJetSource I O E n d)
    (hz : mixedCoveredJetChart U o b hb bW d z =
      physicalCubeRowSample U d (fun _ => Subtype.val) p hm v)
    (s : Finset (Fin dim)) (j : Fin m) :
    (QuotientAddGroup.mk (physicalEuclideanSitePoint U p hm
      (fun x => (physicalCubeVertexValue v s x : ℝ)) j) : euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
          (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1 := by
  sorry

end Erdos3.BooleanCubeKernel

end

end OAI
end
