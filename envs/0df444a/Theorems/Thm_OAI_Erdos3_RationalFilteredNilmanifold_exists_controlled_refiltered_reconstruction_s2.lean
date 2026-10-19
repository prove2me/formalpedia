-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_controlled_refiltered_reconstruction_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_reconstruction_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:00:41.333469+00:00
-- url     : https://prove2.me/theorems/ee0d9055-8945-4ba7-b339-7f23915726a1
-- title:
--   Controlled reconstruction of a product rational filtered nilmanifold along a graded refiltration
-- statement:
--   Let $s$ and $k$ be natural numbers. Then there is a natural number $C \ge 2$ with the following property (all types below in the universe level $u$ of the statement, except $\kappa$, which is arbitrary).
--
--   Let $\iota$ be a finite type with decidable equality, with $|\iota|$ elements. For each $i \in \iota$ let $L_i$ be a Lie algebra over $\mathbb{Q}$ whose realification $\mathbb{R} \otimes_{\mathbb{Q}} L_i$ carries a Hausdorff topology making it a topological additive group with continuous real scalar multiplication. Let $\kappa$ be a finite type with $|\kappa|$ elements, $d : \iota \to \mathbb{N}$, and for each $i$ let $D_i$ be a `RationalFilteredNilmanifold (L i) (s+1) (d i)`. This is a structure defined by OpenAI consisting of a nilpotent Lie filtration of $L_i$ of step $s+1$ (decreasing layers $\mathrm{layer}_1 = L_i \supseteq \mathrm{layer}_2 \supseteq \cdots$ with $[\mathrm{layer}_j, \mathrm{layer}_l] \subseteq \mathrm{layer}_{j+l}$ and the layer after step $s+1$ zero), a $\mathbb{Q}$-basis of $L_i$ indexed by $\{0, \dots, d_i - 1\}$, bases of the layers, a lattice subgroup of the associated group, and a positive integer grid size $g$ such that, in the basis coordinates of the associated Baker–Campbell–Hausdorff group, the lattice contains the scaled integer grid of size $g$ and is contained in the grid of denominators $g$. Let $a \in \iota$, and let $w_i : \{0, \dots, d_i - 1\} \to \mathbb{N}$ be weights such that for all $i$ and $j$, $\mathrm{layer}_j$ of $D_i$ equals the $\mathbb{Q}$-span of the basis vectors $b$ with $j \le w_i(b)$. Let `pi D` be OpenAI's product nilmanifold of the $D_i$, and $\mathfrak{g}$ the associated graded Lie algebra of its filtration. Let $W$ be a Lie subalgebra of $\mathfrak{g}$ and $v_0 : \kappa \to \mathfrak{g}$ with $\mathbb{Q}$-span of the range of $v_0$ equal to $W$. Let $p$ be a real number. Assume:
--   - $0 \le p$, $|\iota| \le p$ and $|\kappa| \le p$;
--   - `(D i).GeometryComplexityLE p` for every $i$ (OpenAI: the dimension is at most $p$, the grid size is at most $e^{p}$, and every structure constant of the basis and every basis coordinate of every layer-basis vector has rational log-height at most $p$, where the rational log-height of $m/n$ in lowest terms is $\log\max(|m|, n)$);
--   - every coordinate of every $v_0(\kappa')$ in the basis of $\mathfrak{g}$ induced (by OpenAI's `associatedGradedBasis`) from the product basis of `pi D` with the product weights has rational log-height at most $p$;
--   - $q$ is a natural number with $0 < q \le e^{p}$.
--
--   Write $\mathfrak{h}$ for `(pi D).filtration.gradedRefiltrationSubalgebra W`, a Lie subalgebra of $\prod_i L_i$ defined by OpenAI as the first layer of the graded refiltration of the product filtration relative to $W$, and $n_{\mathfrak{h}} = \dim_{\mathbb{Q}} \mathfrak{h}$. Then there exists $E$ = a `RationalFilteredNilmanifold 𝔥 (s+1) n_𝔥` such that
--   - the filtration of $E$ is OpenAI's graded refiltration `(pi D).filtration.gradedRefiltration W`;
--   - the lattice of $E$ is the preimage of the lattice of `pi D` under the group homomorphism induced by the inclusion $\mathfrak{h} \hookrightarrow \prod_i L_i$;
--   - `E.GeometryComplexityLE ((p + C)^C)`;
--
--   and there exist a natural number $n \le n_{\mathfrak{h}}$ and $Q$ = a `RationalFilteredNilmanifold (𝔥 ⧸ I) s n`, where $I$ is the ideal given by layer $s+1$ of the filtration of $E$, such that
--   - the filtration of $Q$ is the quotient filtration `E.filtration.quotientTop` and the lattice of $Q$ is the image of the lattice of $E$ under the quotient group homomorphism;
--   - `Q.GeometryComplexityLE ((p + C)^C)`;
--   - `(nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C)^C)`, where `nativeRefilteredTarget D a W E Q` is the OpenAI product nilmanifold of $Q$ (viewed with step $s+1$) and the $D_i$ for $i \ne a$;
--   - `RefilteredRecoveryFamily D a W E Q p q k ((p + C)^C)` holds. This is a proposition defined by OpenAI saying, with $\mathrm{cost} = (p+C)^C$ and $T$ = `nativeRefilteredTarget D a W E Q`: there are a subgroup $\Lambda$ of the lattice of $T$ which is characteristic, normal and of finite index at most $e^{\mathrm{cost}}$ in it, and a grid size $B > 0$ for $\Lambda$, such that the nilmanifold $V$ obtained from $T$ by replacing its lattice by $\Lambda$ satisfies `V.GeometryComplexityLE cost`, and such that for every family $\eta = (\eta_j)_{j}$ (indexed by any type in universe $u$) of $\mathbb{Q}$-linear functionals on the $L_i$ whose realifications vanish on the real layer $s+1$ of the graded refiltration, all elements $l, r$ of the real group of $D_a$ with the real basis coordinates of $l$ bounded in absolute value by $\exp((p+2)^k)$ and the coordinates of $r$ in the real denominator grid of $q$, and every function $S$ on the nilmanifold of $D_a$ which is real, $[0,1]$-valued, $\ell$-Lipschitz with $\ell \le e^{p}$, and invariant under left multiplication by every element $z$ of the realified layer $s+1$ of the filtration of $D_a$ with $\eta_j(a)(z) = 0$ (realified) for all $j$, there is a real, $[0,1]$-valued function $v$ on the nilmanifold of $V$ of norm at most $1$ that is $K$-Lipschitz with $K \le e^{\mathrm{cost}}$ and satisfies $v(\overline{\phi(x)}) = S(\overline{l\,\psi(x)\,r})$ for every $x$ in the real group of $E$, where $\phi$ is the realification of OpenAI's native refiltered map from $E$ to $T$ and $\psi$ the realification of OpenAI's refiltered component map from $E$ to $D_a$ (bars denote the classes in the respective nilmanifolds).
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_reconstruction_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_reconstruction` (in `lean/OAI/Combinatorics/Progressions/Estimates/ControlledRefilteredCyclicExpansion.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B192` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ControlledRefilteredCyclicExpansion.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_reconstruction)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B192

section

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_refiltered_reconstruction_s2 (s k : ℕ) :
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
            RefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end
