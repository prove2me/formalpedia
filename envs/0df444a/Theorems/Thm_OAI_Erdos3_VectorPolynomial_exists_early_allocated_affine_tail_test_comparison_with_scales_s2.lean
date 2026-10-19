-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_tail_test_comparison_with_scales_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_tail_test_comparison_with_scales_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:52.360731+00:00
-- url     : https://prove2.me/theorems/6442793e-d199-4c33-b4de-d64780c174f3
-- title:
--   Explicit source radii and tolerance for which the averaged sliced profile ideal matches the normalized long-jet law against bounded tests
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \operatorname{Fin} m$) finite types, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type $B_a$ to each axis $a$ of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$; the degree of $(j, \cdot)$ is $j+1$). Let $\alpha$ be a finite type with decidable equality, $O_j$ nonempty finite types, and $\mathrm{rows}_j : O_j \to \operatorname{Finset} \alpha$ injective (hrows) with $\#\mathrm{rows}_j(o) \le j+1$ for all $j, o$ (hcard). (All named objects are defined by OpenAI.)
--
--   Let $\psi : \mathbb{R} \to \mathbb{R}$ be $C^\infty$ with values in $[0,1]$, $\psi(t) = 0$ for $|t| \le 1$ and $\psi(t) = 1$ for $|t| \ge 2$. Let $A, T \ge 0$ be such that $\psi$ is $A$-Lipschitz and Mathlib's `Real.smoothTransition` is $T$-Lipschitz. Let $\mathrm{block}_a : O_j \to B_a$ be injective for each axis $a = (j, \cdot)$. Let $\delta, \varepsilon$ be reals with $0 < \delta \le 1$ and $\varepsilon > 0$. Then there is a real $\rho_{\min} > 0$ and a function $\rho$ from predicates on axes to $\mathbb{R}_{\ge 0}$ such that:
--   - for every predicate $P$: $\rho_{\min} \le \rho(P) \le 1$, and $\rho(P)$ equals `partitionedAffineSourceRadius (layerSamplerDegree I n) P A T δ ε` (with the axes not satisfying $P$ carrying row types $O_j$);
--   - and there is a real $t$ with $0 < t \le 1$ and $t$ = `allocatedAffineSourceTolerance B A T δ ε` (the minimum over predicates $P$ of OpenAI's partitioned affine source tolerance),
--
--   such that the following holds. Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $\mathrm{basis}_j$ a real basis indexed by $\operatorname{Fin} n_j$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ inside $\mathbb{R}^{J_j}$), $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (with positive natural number `S.value`). Assume $\sigma_j \le t$ for all $j$. Write `grid` for the predicate `allocatedGridAxis U basis S.value` on axes. Let $x : G \to$ `IntegerScalarCubeBox α S.value`, $u$ a principal axis tuple on the grid axes, and $\mathrm{center}, \mathrm{width}$ real functions on `PrincipalAxisParameter (fun a => ¬ grid a)` (the joint block parameters of the non-grid axes) with $\delta \le |\mathrm{width}(i)|$ and $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$ for all $i$. Let $f$ be a measurable real function of real vectors $v$ indexed by pairs $o = (a, k)$ with $a = (j, \cdot)$ a non-grid axis and $k \in O_j$, with $|f(v)| \le 1$ for all $v$. Then
--   $$\Bigl| \int \mathcal{I}(v)\, f\bigl(o \mapsto R_{j(o)}\, v_o\bigr)\, dv - \int f\Bigl(\texttt{allocatedNormalizedLongJetMap B U basis S x u rows}\ \bigl(i \mapsto \mathrm{center}(i) + \mathrm{width}(i)\, p_2(i)\bigr)\ p_1\Bigr)\, d(\mu \otimes \beta)(p) \Bigr| \le \varepsilon,$$
--   where the first integral is against Lebesgue measure, $j(o)$ is the degree index of the axis of $o$, $\mathcal{I}$ = `activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid (rows restricted to non-grid axes) (ρ grid) center width` (OpenAI's mixture, over the unit coefficient source, of sliced profile ideals); $\mu$ = `unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid)` (density $\prod \psi_0(r_e)$ with respect to Lebesgue measure, $\psi_0$ OpenAI's smooth probability profile, on the coefficient slots of the non-grid axes); $\beta$ = `jointBooleanSource` (OpenAI's product of block cube measures over the non-grid axes); and `allocatedNormalizedLongJetMap` maps a parameter and coefficients to the family, over non-grid axes, of normalized profile jets.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_tail_test_comparison_with_scales_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_tail_test_comparison_with_scales` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean (declaration OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_tail_test_comparison_with_scales)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_tail_test_comparison_with_scales_s2
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T δ ε) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T δ ε ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
        (center width : (PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ f : ((Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ, Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width v * f (fun o => R o.1.val.1 * v o)) -
        ∫ p, f (allocatedNormalizedLongJetMap B U basis S x u rows
          (fun i => center i + width i * p.2 i) p.1)
          ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value))).prod
            (jointBooleanSource (B := fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (α := α) (fun a => (layerSamplerDegree I n) a.val))| ≤ ε := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
