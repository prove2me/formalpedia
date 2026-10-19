-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_anchored_option_mode_factorization_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_option_mode_factorization_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:53:24.263072+00:00
-- url     : https://prove2.me/theorems/30acae74-c1f8-4c36-a825-5be3091586ec
-- title:
--   A biased anchored four-term nilsequence correlation yields a graded rational subalgebra and a fixed product orbit factorization
-- statement:
--   Let $s \ge 1$ be a natural number. Then there is a natural number $C \ge 2$ with the following property.
--
--   Let $J$ and $\sigma$ be finite types ($\sigma$ with decidable equality), and index a family of nilmanifolds by $I = $ `Option (Option J ⊕ J)`, whose elements are `none` (the anchor), `some (inl none)` (the second anchor), `some (inl (some j))` and `some (inr j)` for $j \in J$. For each $i \in I$ let $L_i$ be a Lie algebra over $\mathbb{Q}$, $d_i$ a natural number, and suppose each realification $\mathbb{R} \otimes_{\mathbb{Q}} L_i$, and also $\mathbb{R} \otimes_{\mathbb{Q}} \prod_i L_i$, carries a Hausdorff topology making it a topological additive group with continuous real scalar multiplication. Let $D_i$ be a `RationalFilteredNilmanifold (L i) s (d i)` (a structure defined by OpenAI: a nilpotent Lie filtration of $L_i$ of step $s$, a $\mathbb{Q}$-basis of $L_i$ indexed by $\{0,\dots,d_i-1\}$, bases of the layers, a lattice subgroup and a positive grid parameter sandwiching the lattice coordinates).
--
--   Let all the following be `Niltest`s with multidegree weight $1$ in each of the $\sigma$ variables (a `Niltest`, defined by OpenAI, consists of a polynomial orbit in the real group of the nilmanifold, a complex-valued observable on the nilmanifold, a norm bound and a Lipschitz bound): $P$ and $U_j$ ($j \in J$) on $D_{\mathrm{none}}$; $P_0$ and $V_j$ on $D_{\mathrm{some(inl\,none)}}$; $A_j$ on $D_{\mathrm{some(inl(some\,j))}}$; $B_j$ on $D_{\mathrm{some(inr\,j)}}$. Let $\eta_j : L_{\mathrm{none}} \to \mathbb{Q}$ and $\theta_j : L_{\mathrm{some(inl\,none)}} \to \mathbb{Q}$ be $\mathbb{Q}$-linear functionals. Let $p$ be a real number. Assume:
--   - $2 \le p$, $|I| \le p$ and $|\sigma| \le p$;
--   - every $D_i$ satisfies `GeometryComplexityLE p` (defined by OpenAI: $d_i \le p$, grid $\le e^p$, and every Lie structure constant in the basis and every basis coordinate of the layer bases has `rationalLogHeight` at most $p$, where `rationalLogHeight q` $= \log\max(|\mathrm{num}\,q|, \mathrm{den}\,q)$);
--   - for every $j$: $U_j$ satisfies `ComplexityLE p` (defined by OpenAI: the nilmanifold satisfies `GeometryComplexityLE p` and $\log(2 + \text{normBound} + \text{lipBound}) \le p$), $U_j$ has the same orbit as $P$, and the norm bound of $U_j$ is at most $1$; likewise $V_j$ satisfies `ComplexityLE p`, has the same orbit as $P_0$, and norm bound at most $1$; $A_j$ and $B_j$ satisfy `ComplexityLE p` and have norm bound at most $1$;
--   - for all $j, k$: `rationalLogHeight` $(\eta_j(b_k)) \le p$, where $b_k$ is the $k$-th basis vector of $D_{\mathrm{none}}$, and `rationalLogHeight` $(\theta_j(b'_k)) \le p$, where $b'_k$ is the $k$-th basis vector of $D_{\mathrm{some(inl\,none)}}$;
--   - (vertical characters) for all $j$, every $z$ in the $s$-th subgroup of the realified filtration of $D_{\mathrm{none}}$, and every point $x$ of the nilmanifold, the observable of $U_j$ satisfies $U_j(z \cdot x) = e\bigl(\eta_j^{\mathbb{R}}(\log z)\bigr)\,U_j(x)$, where $\eta_j^{\mathbb{R}}$ = `realifyFunctional (eta j)` is the real-linear extension, $\log z$ is the Lie-algebra coordinate of $z$ and $e(x) = e^{2\pi i x}$ (the character of $\mathbb{R}/\mathbb{Z}$); likewise for $V_j$ with $\theta_j$ on $D_{\mathrm{some(inl\,none)}}$.
--
--   Further let `weight i : Fin (d i) → ℕ` be weights such that, for all $i$ and all $j$, the $j$-th layer of the filtration of $D_i$ is the $\mathbb{Q}$-span of the basis vectors of $D_i$ of weight at least $j$. Let `origin j : σ → ℤ` and `lengths j : σ → ℕ` with all `lengths j i` $> 0$, and assume for every $j$ the bias bound
--   $$e^{-p} \le \Bigl|\mathop{\mathbb{E}}_{x \in Q_j} U_j(x)\,\overline{V_j(x)}\,A_j(x)\,B_j(x)\Bigr|,$$
--   where $Q_j$ = `translatedIntegerBox (origin j) (lengths j)` is the integer box $\{x : \mathrm{origin}_j(i) \le x_i < \mathrm{origin}_j(i) + \mathrm{lengths}_j(i)\}$ and $T(x)$ denotes the `eval` of a Niltest at the integer point $x$ (its observable applied to the orbit at $x$). Finally let `side : σ → ℝ` with $e^{(p+C)^C} \le \mathrm{side}(i)$ for all $i$, and $e^{-p}\,\mathrm{side}(i) \le \mathrm{lengths}_j(i)$ for all $j, i$.
--
--   Let $\omega$ = `productBasisWeight weight` (the weight function on the product basis of the product nilmanifold `pi D`, induced from the weights of the factors), and let $\beta$ be the basis of the associated graded Lie algebra of the filtration of `pi D` obtained from the product basis and $\omega$ (`associatedGradedBasis`, using the layer-span property of the product given by `pi_layer_span`). Then there exist a $\mathbb{Q}$-Lie subalgebra $W$ of the associated graded Lie algebra of `pi D`, vectors $v_1, \dots, v_n$ in it with $n = \sum_i d_i$, and a natural number $m$ such that:
--   - the $\mathbb{Q}$-span of the $v_k$ is $W$;
--   - $W$ is graded with respect to $\beta$ and $\omega$ (`BasisGradedSubmodule`: every graded component, in the coordinates of $\beta$, of an element of $W$ lies in $W$);
--   - every coordinate of every $v_k$ in the basis $\beta$ has `rationalLogHeight` at most $(p+C)^C$;
--   - $0 < m \le e^{(p+C)^C}$;
--   - `HasFixedProductOrbitFactors D none (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit) eta side ((p + C) ^ C) m W` holds. Here `anchoredOptionReferenceData P P₀ A B` is the family of Niltests equal to $P$ at `none`, $P_0$ at `some (inl none)`, $A_j$ at `some (inl (some j))` and $B_j$ at `some (inr j)`; and `HasFixedProductOrbitFactors`, defined by OpenAI, asserts the existence of frequency functionals on each factor, extending $\eta_j$ at the anchor and vanishing (after realification) on the graded refiltration layer of $W$ at level $s$, together with a factorization of the product of these orbits as (slow part) $\cdot$ (middle part) $\cdot$ (rational part on the grid of modulus $m$) $\cdot$ (a lattice element), with the slow part satisfying `PolynomialSlowBound` at scales `side` and $e^{(p+C)^C}$, the rational part satisfying `PolynomialRationalGrid` with modulus $m$, the middle and rational parts having zero constant coefficient, every coefficient of the middle part of degree $a$ lying in the real graded refiltration layer of $W$ at level $a$, and every value of the middle part lying in the realification of the graded refiltration subalgebra of $W$.
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_option_mode_factorization_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_option_mode_factorization` (in `lean/OAI/Combinatorics/Progressions/Estimates/NativeDetectorContradiction.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B161`, `OAIE3v2B174` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/NativeDetectorContradiction.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_option_mode_factorization)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B174

section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_anchored_option_mode_factorization_s2 (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Option (Option J ⊕ J)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Option (Option J ⊕ J)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (P : (D none).Niltest (fun _ : σ => 1)) (P₀ : (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (U : J → (D none).Niltest (fun _ : σ => 1)) (V : J → (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (some (.inl (some j)))).Niltest (fun _ : σ => 1)) (B : ∀ j, (D (some (.inr j))).Niltest (fun _ : σ => 1))
    (eta : J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Option (Option J ⊕ J)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ j, (U j).ComplexityLE p ∧ (U j).orbit = P.orbit ∧ (U j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ j, (B j).ComplexityLE p ∧ (B j).normBound ≤ 1)
    (_heta : ∀ j k, rationalLogHeight (eta j ((D none).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (some (.inl none))).basis k)) ≤ p)
    (_hvertU : ∀ j z, z ∈ (D none).filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (some (.inl none))).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : J → σ → ℤ) (lengths : J → σ → ℕ) (_hlengths : ∀ j i, 0 < lengths j i)
    (_hbias : ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ j i, Real.exp (-p) * side i ≤ lengths j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal)
        omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
          (p + C) ^ C) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      HasFixedProductOrbitFactors D none
        (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit) eta side ((p + C) ^ C) m W := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end
