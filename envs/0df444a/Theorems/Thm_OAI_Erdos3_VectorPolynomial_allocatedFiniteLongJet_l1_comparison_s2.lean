-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiniteLongJet_l1_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFiniteLongJet_l1_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:19:40.684244+00:00
-- url     : https://prove2.me/theorems/53228364-e2c1-4993-82ea-89d55cb3edf7
-- title:
--   A pointwise bound between the scaled long-jet mixture and the masked proxy gives an L1 bound against the long-jet reference measure
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type with decidable equality, $I_j$ ($j<m$) finite types with decidable equality, $n : \mathrm{Fin}(m)\to\mathbb{N}$, and $B_a$ finite types with decidable equality indexed by the axes $a$ of `LayerSamplerAxis I n` $= \Sigma_{j<m}(I_j \sqcup \mathrm{Fin}(n_j))$. Let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `basis j` a basis (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}(m) \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$, and `S : LayerSamplerScale B U basis R σ` (OpenAI's sampler scale data, with a positive integer length `S.value`). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (integer points of OpenAI's scalar cube box of length `S.value`). Write `grid` for the predicate `allocatedGridAxis U basis S.value` on axes (true exactly on integer axes $(j, i)$ with $i \in \mathrm{Fin}(n_j)$ whose basis axis scale is at most $\texttt{S.value}^{\texttt{layerTailDegree}\ m + 1}$) and `sides` for `allocatedPrincipalSides B U basis S`. Let $u$ be a point of `PrincipalAxisTuples grid sides` (OpenAI's integer tuples on the grid axes). Let $O_j$ be finite types with decidable equality, `rows j : O j → Finset α`, and embeddings `s j : O j ↪ BoundedIntegerExponent G (j+1)`, such that for each $j$ the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` with columns `s j` has nonzero determinant (hypothesis `hA`). Let $M$ be a natural number with $M > 0$ and assume, for every $j$, `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` (OpenAI's bound on the operator norm of the inverse of the fixed pivot map by `kernelJetInverseAllowance … (1/M)`). Let $P \ge 0$ be real with $M \le e^{P}$, and for all $j$: $R_j \le e^{P}$, $R_j^{-1} \le e^{P}$, $\sigma_j^{-1} \le e^{P}$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^{P}$, and $\sigma_j \le 1$.
--
--   **Objects.** Let $T = \exp(\texttt{allocatedJetSupportLog B α O P})$, $Q = \prod_a$ `allocatedLongJetOutputScale B U basis S a` (product over non-grid axes $a$; the factor is $1$ on continuous axes and $(\text{basis axis scale})^{|O_j|}$ on an integer axis $(j,i)$), and $V = (2T + 1)^{K}$ with $K = |\Sigma_{a} O_{a.1}|$ (sum over all axes). Let `reference` be the measure `allocatedLongJetReference B U basis S O` on `AllocatedLongJetRows B U basis S O` (the product over non-grid axes of OpenAI's per-axis reference measures on coefficient jet rows). Let $w$ be finite probability weights on `PrincipalAxisTuples (fun a => ¬grid a) sides`, let `modulus` be a natural number and `residue j` a matrix over $\mathbb{Z}/\texttt{modulus}$ indexed by $O_j$ and `AllocatedNonkernelCoefficient B j`. For $v$ a tuple and $z$ a row family define:
--   - $\mathrm{density}(v, z)$ = `allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z` (OpenAI's product density over non-grid axes);
--   - $\mathrm{target}(v, z) = \prod_a$ `allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a)`, where `normalized` is `principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides)` (integer tuple entries divided by their side lengths);
--   - $\mathrm{proxy}(z) = \bigl(\prod_a \texttt{allocatedLongJetMask B U basis S x rows modulus residue}\ a\ (z_a)\bigr)\cdot \mathbb{E}_{w}[v \mapsto \mathrm{target}(v,z)]$, where $\mathbb{E}_w$ is the mean under $w$.
--
--   **Statement.** Let $\varepsilon \ge 0$ and assume that for every $z$,
--   $$\bigl|\mathbb{E}_w[v \mapsto Q\cdot \mathrm{density}(v,z)] - \mathrm{proxy}(z)\bigr| \le \varepsilon.$$
--   Then $z \mapsto \mathrm{proxy}(z)/Q$ is integrable with respect to `reference`, and
--   $$\int \bigl|\mathbb{E}_w[v \mapsto \mathrm{density}(v,z)] - \mathrm{proxy}(z)/Q\bigr|\, d\,\mathrm{reference}(z) \le V\varepsilon.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFiniteLongJet_l1_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFiniteLongJet_l1_comparison` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteCoefficientL1.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B194`, `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteCoefficientL1.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFiniteLongJet_l1_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "T" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "Q" => ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a
local notation "V" => (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))
local notation "reference" => allocatedLongJetReference B U basis S O

variable (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S)))
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "density" => (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1)
local notation "normalized" => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides)
local notation "target" => (fun (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
  (z : AllocatedLongJetRows B U basis S O) =>
  ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a))
local notation "proxy" => (fun (z : AllocatedLongJetRows B U basis S O) =>
  (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) * w.mean (fun v => target v z))

include hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedFiniteLongJet_l1_comparison_s2 {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ z, |w.mean (fun v => Q * density v z) - proxy z| ≤ ε) :
    Integrable (fun z => proxy z/Q) reference ∧
      (∫ z, |w.mean (fun v => density v z)-proxy z/Q| ∂reference) ≤ V*ε := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
