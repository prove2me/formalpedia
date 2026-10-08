-- Prove2me | Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_jet_period
-- name    : OAI.Erdos3.canonicalSlicedModulus_jet_period
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:20:48.936983+00:00
-- url     : https://prove2.me/theorems/7b4c8951-fd87-419c-88bd-f79026149d10
-- title:
--   The canonical sliced modulus is a period of every bounded-degree integer jet
-- statement:
--   Let $\alpha,G,X$ be finite types ($\alpha$ with decidable equality), $L,M$ natural numbers, $\mathrm{selection} : \alpha\hookrightarrow G$ an embedding, $\mathrm{stride} : X\to\mathbb{N}$, and $\mathrm{height}$ a natural number. Let $x : G\to$ `IntegerScalarCubeBox α L` (functions from $\mathrm{Option}\ \alpha$ to integers in $[-L,L)$) satisfy `GoodScalarKernelTuple selection (1/M) M x` (the predicate that OpenAI's `normalizedScalarCubeMinor selection x` has absolute value greater than $1/M$ and the range of the integer matrix `scalarCubeDifferenceMatrix x` satisfies `HasBoundedScalarPeriod … M`). Let $O$ be a finite type, $\mathrm{degree}$ a natural number with $\mathrm{degree}\le\mathrm{height}+1$, and $\mathrm{rows} : O\to\mathrm{Finset}\ \alpha$ an injective map with $|\mathrm{rows}(o)|\le\mathrm{degree}$ for every $o$. Let $m$ be `canonicalSlicedModulus selection stride height x` (taken with this $M$), as an integer. Then the lattice `integerScalarLattice O m` $=m\,\mathbb{Z}^O$ is contained in the range (column span over $\mathbb{Z}$, as a $\mathbb{Z}$-submodule of $\mathbb{Z}^O$) of the integer matrix `scalarKernelIntegerJet x degree rows`, OpenAI's bounded-degree integer jet matrix with rows indexed by $O$.
--
--   Lean: `OAI.Erdos3.canonicalSlicedModulus_jet_period` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedDetectedCanonicalPeriod.lean#L80

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

end Erdos3

end

section

namespace Erdos3

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_jet_period
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    {O : Type*} [Fintype O] (degree : ℕ) (hdegree : degree ≤ height + 1)
    (rows : O → Finset α) (hinj : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ degree) :
    integerScalarLattice O (canonicalSlicedModulus (M := M) selection stride height x : ℤ) ≤
      (scalarKernelIntegerJet x degree rows).mulVecLin.range := by
  sorry

end Erdos3
end
end OAI
