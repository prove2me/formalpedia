-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_retained_lattice_normalization_s2
-- name    : OAI.Erdos3.exists_retained_lattice_normalization_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:48:48.760389+00:00
-- url     : https://prove2.me/theorems/3a60518f-8210-4c2f-b287-c770adbcbc08
-- title:
--   Simultaneous symbol factorizations in several graded subalgebras give a normalized factorization of the polynomial orbit in their intersection
-- statement:
--   Let $s$ be a natural number. Then there is a natural number $C \ge 2$ (depending only on $s$) with the following property.
--
--   **Data.** Let $\sigma$ and $J$ be finite types, $L$ a Lie algebra over $\mathbb{Q}$ with the real vector space $\mathbb{R} \otimes_{\mathbb{Q}} L$ given a topology making it a topological additive group with continuous scalar multiplication, $d \in \mathbb{N}$, and $D$ a `RationalFilteredNilmanifold L s d` (a structure defined by OpenAI: a nilpotent Lie filtration of $L$ of length $s$, a $\mathbb{Q}$-basis $(e_i)_{i \in \mathrm{Fin}\,d}$ of $L$, layer bases, a lattice subgroup and a grid). Let $w : \mathrm{Fin}\,d \to \mathbb{N}$ be weights such that (hypothesis $h_F$) for every $j$ the $j$-th layer of the filtration is the $\mathbb{Q}$-span of $\{e_i : j \le w_i\}$. Let $\mathfrak{g}$ = `D.filtration.AssociatedGraded` (the associated graded Lie algebra, defined by OpenAI) and $\beta$ = `D.filtration.associatedGradedBasis D.basis w h_F`, its basis indexed by $\mathrm{Fin}\,d$. For each $j \in J$ let $U_j$ be a Lie subalgebra of $\mathfrak{g}$, $v_j : \mathrm{Fin}\,d \to \mathfrak{g}$, and $n_j \in \mathbb{N}$. Let $p$ be a real number.
--
--   **Hypotheses.**
--   - $0 \le p$ and `D.GeometryComplexityLE p` (defined by OpenAI: $d \le p$, $\mathrm{grid} \le e^{p}$, and all structure constants and layer-basis coordinates are rationals of logarithmic height at most $p$);
--   - $|\sigma| \le p$ and $|J| \le p$;
--   - for every $j$, the $\mathbb{Q}$-span of the vectors $v_j(i)$ is $U_j$, and $U_j$ is graded with respect to $\beta$ and $w$ (`BasisGradedSubmodule`: $U_j$ is closed under each grade projection);
--   - every $\beta$-coordinate of every $v_j(i)$ is a rational of logarithmic height `rationalLogHeight` $\log \max(|\text{numerator}|, \text{denominator})$ at most $p$;
--   - $0 < n_j \le e^{p}$ for every $j$;
--   - $A : \sigma \to \mathbb{R}$ with $\exp((p + C)^C) \le A_i$ for every $i$;
--   - $g$ is an element of the group of the adapted polynomial filtration (in the variables $\sigma$, all of weight $1$) of the realified filtration of $D$, i.e. a polynomial orbit, and for every $j$, `D.filtration.SymbolFactorizationIn D.basis w h_F A X p (n j) (U j)` holds for $X$ = `D.filtration.realPolynomialSymbolHom D.basis w h_F 1 g`, the image of $g$ in the real polynomial symbol group (defined by OpenAI: $X = E P R$ with $E$ slow, its symbol coordinates bounded by $e^{p} / \prod_i A_i^{\alpha_i}$ at each monomial $\alpha$, $R$ with symbol coordinates in $\frac{1}{n_j}\mathbb{Z}$, and $P$ pointwise in $U_j$).
--
--   **Conclusion.** Writing $U = \bigcap_j U_j$ and $Q = (p + C)^C$, there exist $v_0 : \mathrm{Fin}\,d \to \mathfrak{g}$, $m \in \mathbb{N}$, an element $\kappa$ of the real group of $D$, and elements $E, b, R$ of the same adapted polynomial group as $g$ such that:
--   1. the $\mathbb{Q}$-span of the $v_0(i)$ is $U$, and $U$ is graded with respect to $\beta$ and $w$;
--   2. every $\beta$-coordinate of every $v_0(i)$ has logarithmic height at most $Q$;
--   3. $0 < m \le e^{Q}$ and $n_j \mid m$ for every $j$;
--   4. $\kappa$ lies in the real lattice of $D$;
--   5. $E \cdot b \cdot R \cdot \iota(\kappa) = g$, where $\iota$ = `adaptedConstantGroupHom` embeds the real group as constant polynomials;
--   6. for every monomial $\alpha$ in $\sigma$ and every $i \in \mathrm{Fin}\,d$, the $i$-th coordinate (with respect to the basis $(1 \otimes e_i)$ of $\mathbb{R} \otimes L$) of the $\alpha$-coefficient of the vector polynomial $E.\mathrm{coord}$ has absolute value at most $e^{Q} / \texttt{monomialScale}\ A\ \alpha$, where `monomialScale A α` $= \prod_i A_i^{\alpha_i}$;
--   7. all these coordinates of all coefficients of $R.\mathrm{coord}$ lie in $\frac{1}{m}\mathbb{Z}$ (`realDenominatorGrid m`);
--   8. the constant coefficients of $b.\mathrm{coord}$ and of $R.\mathrm{coord}$ are $0$;
--   9. for every monomial $\alpha$, the $\alpha$-coefficient of $b.\mathrm{coord}$ lies in `D.filtration.realGradedRefiltrationLayer U |α|` (the real base change of the graded refiltration layer of $U$ of index the total degree $|\alpha|$; defined by OpenAI);
--   10. for every $t \in \mathbb{R}^\sigma$, the evaluation of $b.\mathrm{coord}$ at $t$ lies in the realification of the Lie subalgebra `D.filtration.gradedRefiltrationSubalgebra U` (defined by OpenAI).
--
--   Lean: `OAI.Erdos3.exists_retained_lattice_normalization_s2`, which states OpenAI's `OAI.Erdos3.exists_retained_lattice_normalization` (in `lean/OAI/Combinatorics/Progressions/Lattices/RetainedLatticeNormalization.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B128`, `OAIE3v2B129` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/RetainedLatticeNormalization.lean (declaration OAI.Erdos3.exists_retained_lattice_normalization)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129

section

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_retained_lattice_normalization_s2 (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n : J → ℕ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) := by
  sorry

end Erdos3

end

end OAI
end
