-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_controlled_refiltered_residue_expansion_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_residue_expansion_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:01:59.030462+00:00
-- url     : https://prove2.me/theorems/76c31c84-f761-4c08-82b6-28b05a6d0cd7
-- title:
--   Graded refiltration of a product of rational filtered nilmanifolds admits a residue expansion with quasipolynomially controlled complexity
-- statement:
--   Let $s, r$ be natural numbers. Then there is a natural number $C \ge 2$ with the following property.
--
--   Let $\iota$ be a finite type with decidable equality, and for each $i \in \iota$ let $L_i$ be a Lie algebra over $\mathbb{Q}$ such that $\mathbb{R} \otimes_{\mathbb{Q}} L_i$ carries a Hausdorff topology making it a topological additive group with continuous real scalar multiplication. Let $\kappa$ be a finite type, $d : \iota \to \mathbb{N}$, and for each $i$ let $D_i$ be a `RationalFilteredNilmanifold (L i) (s + 1) (d i)` (defined by OpenAI: a nilpotent Lie filtration of $L_i$ of step $s+1$, a $\mathbb{Q}$-basis of $L_i$ indexed by $\mathrm{Fin}\ (d\ i)$, bases of the filtration layers, a lattice subgroup of the associated Malcev-type group, and a positive integer grid sandwiching the lattice). Write `pi D` for the product rational filtered nilmanifold on $\prod_i L_i$, defined by OpenAI. Let $a \in \iota$, and let $w_i : \mathrm{Fin}\ (d\ i) \to \mathbb{N}$ be weights such that for all $i$ and $j$, the $j$-th filtration layer of $D_i$ is the $\mathbb{Q}$-span of the basis vectors $(D_i).\mathrm{basis}(b)$ with $j \le w_i(b)$. Let $W$ be a Lie subalgebra of the associated graded Lie algebra of the filtration of `pi D`, and $v_0 : \kappa \to$ (that associated graded algebra) a family whose $\mathbb{Q}$-span is $W$. Let $p$ be a real number. Suppose:
--
--   - $1 \le p$ and $|\iota| \le p$;
--   - for every $i$, `(D i).GeometryComplexityLE p` holds (defined by OpenAI: the dimension is at most $p$, the grid is at most $e^{p}$, and all structure constants and layer-basis coordinates have `rationalLogHeight` at most $p$, where `rationalLogHeight x` $= \log \max(|\mathrm{num}\ x|, \mathrm{den}\ x)$);
--   - $|\kappa| \le p$;
--   - for every $k \in \kappa$ and every index $b$, the `rationalLogHeight` of the $b$-th coordinate of $v_0(k)$ in the basis `associatedGradedBasis` of the associated graded algebra (built by OpenAI from the basis of `pi D` and the product weights `productBasisWeight w`) is at most $p$.
--
--   Then for every natural number $q$ with $0 < q \le e^{p}$ there exist:
--
--   - a natural number $P$ with $0 < P \le e^{(p + C)^C}$;
--   - a `RationalFilteredNilmanifold` $E$ on the Lie algebra $H$ = `(pi D).filtration.gradedRefiltrationSubalgebra W` (a Lie subalgebra of $\prod_i L_i$ defined by OpenAI from $W$), of step $s + 1$ and dimension $\dim_{\mathbb{Q}} H$, whose filtration is `(pi D).filtration.gradedRefiltration W` (the graded refiltration, defined by OpenAI), whose lattice is the preimage of the lattice of `pi D` under the group map induced by the inclusion $H \hookrightarrow \prod_i L_i$, and which satisfies `E.GeometryComplexityLE ((p + C)^C)`;
--   - a natural number $n \le \dim_{\mathbb{Q}} H$ and a `RationalFilteredNilmanifold` $Q$ on the quotient Lie algebra $H / I$, where $I$ = `E.filtration.layerIdeal (s + 1)` is the top layer of the filtration of $E$ viewed as an ideal, of step $s$ and dimension $n$, whose filtration is the quotient filtration `E.filtration.quotientTop`, whose lattice is the image of the lattice of $E$ under the quotient group homomorphism, and which satisfies `Q.GeometryComplexityLE ((p + C)^C)`;
--
--   such that moreover `(nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C)^C)` holds, where `nativeRefilteredTarget D a W E Q` is the rational filtered nilmanifold defined by OpenAI as the product of $Q$ (raised to step $s+1$) with the factors $D_i$, $i \ne a$; and `RefilteredResidueExpansionSpec D a W E Q p q r P ((p + C)^C)` holds, a predicate defined by OpenAI. Roughly, it asserts that there are refinements $Q'$ of $Q$ and $Z$ of the product of the $D_i$ ($i \ne a$), each with the same filtration and basis and a smaller lattice and with `GeometryComplexityLE ((p + C)^C)`, such that any family of niltests on $D_a$ of complexity at most $p$ whose orbits factor into a slow part (bounded in terms of $e^{(p+2)^r}$), a part on the rational grid of modulus $q$, and a middle part coming from $E$, decomposes, over partitions of unity on $\mathbb{Z}/N$ labelled by residues modulo $P$, as a combination of niltests on $Q'$ of complexity at most $(p + C)^C + 2$, up to an error whose average is at most $e^{(p+C)^C}(\rho + \eta) + 6\rho + 3/N$ (see OpenAI's definition for the exact statement).
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_residue_expansion_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_residue_expansion` (in `lean/OAI/Combinatorics/Progressions/Lattices/ControlledRefilteredResidueExpansion.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B193` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ControlledRefilteredResidueExpansion.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_residue_expansion)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_controlled_refiltered_residue_expansion_s2 (s r : ℕ) :
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
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
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
              RefilteredResidueExpansionSpec D a W E Q p q r P ((p + C) ^ C) := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end
