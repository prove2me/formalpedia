-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_proxy_l1_with_scales
-- name    : OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_proxy_l1_with_scales
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:13:59.83739+00:00
-- url     : https://prove2.me/theorems/076af331-aed3-4c4b-8cc2-82ea1bb9e3f9
-- title:
--   Source radii and a tolerance make the affine long-jet proxy L1-close to the ideal
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), a finite type $\alpha$ with decidable equality, nonempty finite types $O_j$ with decidable equality, and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$ that are injective with $|\mathrm{rows}_j(o)| \le j+1$ for all $j, o$. Let $\psi : \mathbb R \to \mathbb R$ be $C^\infty$ with values in $[0,1]$, $\psi(t) = 0$ for $|t| \le 1$ and $\psi(t) = 1$ for $|t| \ge 2$; let $A, T \ge 0$ be such that $\psi$ is $A$-Lipschitz and Mathlib's `Real.smoothTransition` is $T$-Lipschitz; let $\mathrm{block}_a : O_{a.1} \to B_a$ be injective for every $a$; and let $\delta, \varepsilon$ be reals with $0 < \delta \le 1$ and $0 < \varepsilon$. Then there exist a nonnegative real $\rho_{\min} > 0$ and a function $\rho$ from predicates on `LayerSamplerAxis I n` to nonnegative reals such that, for every predicate $P$, $\rho_{\min} \le \rho(P) \le 1$ and $\rho(P) =$ `partitionedAffineSourceRadius` (with block types $B$, output types $a \mapsto O_{a.1}$ on $\{a \mid \neg P\,a\}$, $\alpha$, degrees `layerSamplerDegree I n`, $P$, $A$, $T$, $\delta$, $\varepsilon$), and there exists a real $t$ with $0 < t \le 1$ and $t =$ `allocatedAffineSourceTolerance B A T δ ε` (with $G$, $O$, $\alpha$), such that the following holds. For all finite types $J_j$, subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j > 0$ and $\sigma_j > 0$, every `LayerSamplerScale` $S$ for $(B, U, \mathrm{basis}, R, \sigma)$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities) with $\sigma_j \le t$ for all $j$, writing grid for `allocatedGridAxis U basis S.value` (a predicate on `LayerSamplerAxis I n`): for every $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), every $u \in$ `PrincipalAxisTuples grid (allocatedPrincipalSides B U basis S)`, all real functions center, width on `PrincipalAxisParameter (¬grid)` with $\delta \le |\mathrm{width}(i)|$ and $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$ for all $i$, and all embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` such that the square submatrix of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)` on the columns $s_j$ has nonzero determinant ($h_A$), we have
--   $$\int \bigl|\,\texttt{diagonalImageDensity}\ (o \mapsto R_{o.1.1.1})\ \Phi\ v - \texttt{allocatedAffineLongJetProxy}\ B\ U\ \mathrm{basis}\ S\ x\ u\ \mathrm{rows}\ s\ h_A\ \mathrm{center}\ \mathrm{width}\ v\,\bigr|\,dv \le \varepsilon,$$
--   where the integral is Lebesgue measure over $v \in \mathbb R^{\Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}} O_{a.1}}$, `diagonalImageDensity d f v` $= (\prod_o |d_o|)^{-1} f(v/d)$ (coordinatewise division), and $\Phi$ is `activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid (a ↦ rows a.1) (ρ grid) center width` (with $G$, $B$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_proxy_l1_with_scales` in `lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean#L21

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_proxy_l1_with_scales
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
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
        (center width : (PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∫ v, |diagonalImageDensity
          (fun o : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) => R o.1.val.1)
          (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
            (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)
            (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width) v -
        allocatedAffineLongJetProxy B U basis S x u rows s hA center width v|) ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
