-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_coveredJetArray_density_law_s2
-- name    : OAI.Erdos3.VectorPolynomial.coveredJetArray_density_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:38:09.938902+00:00
-- url     : https://prove2.me/theorems/4a054505-8534-48d2-847e-7111828b4d12
-- title:
--   Pushing a covered jet-array density through the covered jet chart gives the restricted chart density against Haar measure on the tori
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $m$ be a natural number and $O_j, J_j, I_j, B_j$ ($j < m$) finite types, $n : \mathrm{Fin}(m) \to \mathbb{N}$. Let $U_j \subseteq \mathbb{R}^{J_j}$ be subspaces, $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$, `b j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb{Z}$-span is the projected integer lattice (`hb`), and `bW j` $\mathbb{Z}$-bases (indexed by $B_j$) of the lattice section $\Lambda_j$ of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)`, assumed to be a $\mathbb{Z}$-lattice. Let $d \ge 1$ be a natural number. Let $\nu_j$ be a left-invariant probability measure on the torus `euclideanSubspace (U j)` $/\Lambda_j$ for each $j$.
--
--   Let $\Omega_j(t) \subseteq \mathbb{R}^{J_j}$ (Euclidean space), for $t \in O_j$, be measurable sets contained in `standardLatticeSmallBox (J j)` $= \{x : |x_i| < 1/2\ \forall i\}$. Write $\mathcal{S}$ for the space of pairs $p = (p_1, p_2)$ with $p_1$ assigning to each $j$ a real array $I_j \times O_j \to \mathbb{R}$ and an integer array $\mathrm{Fin}(n_j) \times O_j \to \mathbb{Z}$, and $p_2$ assigning to each $j$ an array $O_j \times B_j \to \mathbb{Z}/d\mathbb{Z}$. Let $f : \mathcal{S} \to \mathbb{R}$ vanish at every $p$ with `mixedCoveredJetCoordinates U o d p` $\notin$ `coveredJetSourceRegion U b d Ω` (the region of chart sources whose normalized lattice points `normalizedLatticePoint (euclideanSubspace (U j)) (b j)` lie in $\Omega_j(t)$ in every slot $(j, t)$).
--
--   Then the push-forward of the measure with density $\max(f, 0)$ (`realDensityMeasure`, i.e. density $\mathrm{ENNReal.ofReal} \circ f$) with respect to `coveredJetArrayReference U d` (the product over $j$ of OpenAI's mixed array reference measures scaled by $\operatorname{covol}(\Lambda_j)^{-|O_j|}$, times the uniform measure on the residue arrays) under the map $p \mapsto$ `coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d p)` equals the measure with density (again via `realDensityMeasure`)
--   $$\texttt{restrictedChartDensity}\ (\texttt{coveredJetChart U b hb bW d})\ (\texttt{coveredJetSourceRegion U b d}\ \Omega)\ 1\ \bigl(x \mapsto f((\texttt{mixedCoveredJetEquiv U o d})^{-1} x)\bigr)$$
--   with respect to the product measure $\prod_j \prod_{t \in O_j} \nu_j$ on `EuclideanJetLayers U O`. Here `restrictedChartDensity q S c g` is the function on the target that equals $c\cdot g(x)$ at a point $q(x)$ with $x \in S$ (well defined when $q$ is injective on $S$) and $0$ off $q(S)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.coveredJetArray_density_law_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.coveredJetArray_density_law` (in `lean/OAI/Combinatorics/Progressions/Probability/MixedCoveredDensityMass.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B092`, `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/MixedCoveredDensityMass.lean (declaration OAI.Erdos3.VectorPolynomial.coveredJetArray_density_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetArray_density_law_s2 (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (f : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ)
    (hf : ∀ p, mixedCoveredJetCoordinates U o d p ∉ coveredJetSourceRegion U b d Ω → f p = 0) :
    (realDensityMeasure (coveredJetArrayReference U d) f).map
      (fun p => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d p)) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun x => f ((mixedCoveredJetEquiv U o d).symm x))) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
