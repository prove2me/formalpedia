-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_controlled_lower_refiltered_reconstruction
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_lower_refiltered_reconstruction
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T06:59:57.127407+00:00
-- url     : https://prove2.me/theorems/977c227e-c37f-4fa0-bb2b-2179a0b117ec
-- title:
--   Controlled refiltered nilmanifold, top quotient and lower recovery family for a product
-- statement:
--   Let $s, k$ be natural numbers (and $u$ a universe level, a section `universe` of the file). Then there is a natural number $C \ge 2$ with the following property. Let $\iota$ be a finite type in universe $u$ with decidable equality; for each $i \in \iota$ let $L_i$ be a $\mathbb{Q}$-Lie algebra in universe $u$, with $\mathbb{R} \otimes_{\mathbb{Q}} L_i$ given a Hausdorff topology making it a topological additive group with continuous real scalar multiplication; let $\kappa$ be a finite type, $d : \iota \to \mathbb{N}$, and $D_i$ a `RationalFilteredNilmanifold (L i) (s+1) (d i)` (OpenAI's structure bundling a nilpotent filtration of length $s+1$, a $\mathbb{Q}$-basis indexed by $\mathrm{Fin}(d_i)$, layer bases, a lattice and a grid). Let $a \in \iota$, and let $w_i : \mathrm{Fin}(d_i) \to \mathbb{N}$ be weights such that each layer $j$ of $D_i$'s filtration is the span of the basis vectors $b$ with $j \le w_i(b)$. Write `pi D` for OpenAI's product rational filtered nilmanifold on $\prod_i L_i$, $\mathfrak{g}$ for its associated graded algebra, and $\beta$ for its basis `associatedGradedBasis` built from the product basis with weights `productBasisWeight w`. Let $W$ be a $\mathbb{Q}$-Lie subalgebra of $\mathfrak{g}$ and $v_0 : \kappa \to \mathfrak{g}$ with span of the range of $v_0$ equal to $W$, and let $p \in \mathbb{R}$. Assume $0 \le p$, $|\iota| \le p$, `(D i).GeometryComplexityLE p` for every $i$ (OpenAI's bound: dimension $\le p$, grid $\le e^p$, log-heights of structure constants and layer-basis coordinates $\le p$), $|\kappa| \le p$, and every $\beta$-coordinate of every $v_0(i)$ has `rationalLogHeight` ($\log\max(|\mathrm{num}|, \mathrm{den})$) at most $p$. Then for every natural $q$ with $0 < q \le e^p$, writing $H$ for `(pi D).filtration.gradedRefiltrationSubalgebra W` (a $\mathbb{Q}$-Lie subalgebra of $\prod_i L_i$), there exist a `RationalFilteredNilmanifold H (s+1) (dim H)` $E$ whose filtration is `(pi D).filtration.gradedRefiltration W`, whose lattice is the preimage of the lattice of `pi D` under the group map induced by the inclusion $H \hookrightarrow \prod_i L_i$, and with `E.GeometryComplexityLE ((p+C)^C)`; a natural number $n \le \dim H$; and a `RationalFilteredNilmanifold` $Q$ of degree $s$ and dimension $n$ on the quotient of $H$ by the top layer ideal $E.\mathrm{filtration.layerIdeal}(s+1)$, whose filtration is `E.filtration.quotientTop`, whose lattice is the image of $E$'s lattice under the quotient map, and with `Q.GeometryComplexityLE ((p+C)^C)`; such that `(nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p+C)^C)` (that target is OpenAI's product of the raised $Q$ with the $D_i$, $i \ne a$) and `LowerRefilteredRecoveryFamily D a W E Q p q k ((p+C)^C)` holds (OpenAI's predicate providing sublattice versions $Q'$ of $Q$ and $Z$ of $\prod_{i \ne a} D_i$ of complexity at most the given cost, through which suitably invariant Lipschitz observables on $D_a$ are recovered with controlled constants).
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_lower_refiltered_reconstruction` in `lean/OAI/Combinatorics/Progressions/Estimates/ControlledRefilteredCyclicExpansion.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B042` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ControlledRefilteredCyclicExpansion.lean#L171

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B042

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_lower_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C) ^ C) ∧
            LowerRefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  sorry

end Erdos3.RationalFilteredNilmanifold
end
end OAI
