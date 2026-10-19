-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedLongJet_ideal_transfer_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSlicedLongJet_ideal_transfer_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:19:48.685459+00:00
-- url     : https://prove2.me/theorems/5cf3d286-131d-4d3f-81ae-c8edc9d7b3b1
-- title:
--   An L1 approximation of the long-profile density by g transfers to an L1 bound between the residue-law averaged long-jet density and g
-- statement:
--   Let $m$ be a natural number, $G$ a finite type with decidable equality, $I_j$ ($j \in \operatorname{Fin} m$) finite types with decidable equality, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type with decidable equality to each axis of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$; the degree of $(j, \cdot)$ is $j+1$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $\mathrm{basis}_j$ a real basis indexed by $\operatorname{Fin} n_j$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ inside $\mathbb{R}^{J_j}$), $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (OpenAI's structure with a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value`, $O_j$ finite types with decidable equality, and $\mathrm{rows}_j : O_j \to \operatorname{Finset} \alpha$. Write `grid` for OpenAI's predicate `allocatedGridAxis U basis S.value` on axes, `tupleIndex` for the triples $(a, \beta, k)$ with $a$ a non-grid axis, $\beta \in B_a$ and $k < \deg a$, and $\ell_j$ for the side length `allocatedPrincipalSides B U basis S` of the triple $j$. (All named objects are defined by OpenAI.)
--
--   Let $M$ be a positive natural number and assume:
--   - $\mathrm{selection} : \alpha \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M) M x` (the normalized scalar cube minor of $x$ along $\mathrm{selection}$ exceeds $1/M$ in absolute value, and the column space of the cube difference matrix has bounded period $M$);
--   - $\#\alpha \le m+1$; each $\mathrm{rows}_j$ is injective; $\#\mathrm{rows}_j(o) \le j+1$ for all $j, o$; $\sigma_j \le 1$ for all $j$;
--   - $P, e, \varepsilon$ are reals with $P \ge 0$, $e \ge 0$, $\varepsilon > 0$, $M \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, $\#\,$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` $+ 1 \le e^P$ for all $j$, $\varepsilon^{-1} \le e^e$, and $\exp(\texttt{allocatedKernelReplacementLog B α O P e}) \le \texttt{S.value}$;
--   - $\mathrm{modulus}$ is a natural number such that, for every $j$, the lattice $\mathrm{modulus} \cdot \mathbb{Z}^{O_j}$ is contained in the image of the integer matrix `scalarKernelIntegerJet x (j+1) rows_j` (hperiod);
--   - $s_j$ is an embedding of $O_j$ into `BoundedIntegerExponent G (j+1)` such that the square submatrix on the columns $s_j$ of `scalarKernelIntegerJet x (j+1) rows_j` has nonzero determinant (hA), and `fixedKernelInverseBound S.positive x (j+1) rows_j (s j) (hA j) (1/M)` holds for each $j$ (hi);
--   - $u$ is a principal axis tuple on the grid axes; $H, \mathrm{step} : \texttt{tupleIndex} \to \mathbb{N}$ and $c : \texttt{tupleIndex} \to \mathbb{Z}$ with $H(j) > 0$ and the progression $\{c(j) + \mathrm{step}(j)\, i : 0 \le i < H(j)\}$ contained in $[0, \ell_j)$; $\mathrm{modulus} > 0$; $r$ assigns to each triple $j$ and each $i \in \operatorname{Option} \alpha$ a residue in $\mathbb{Z}/\mathrm{modulus}$; $(\#\alpha + 1)\cdot \mathrm{modulus} \le H(j)$ for all $j$;
--   - $v_0$ is a principal axis tuple on the non-grid axes with nonzero weight under `law` = `containedProgressionResidueLaw activeB activeDegree ℓ H step c _ hH hsubset modulus hm r hsize` (OpenAI's finite probability law on principal integer tuples, the fiber law of residue-conditioned cube weights mapped into the progressions);
--   - $g$ is a real function on `AllocatedLongJetRows B U basis S O`, integrable for $\lambda$ = `allocatedLongJetReference B U basis S O` (the product over non-grid axes $(j, \cdot)$ of Lebesgue measure on $O_j \to \mathbb{R}$ or counting measure on $O_j \to \mathbb{Z}$), and $E_{\mathrm{ref}}$ is a real number.
--
--   Put $C = \exp(\texttt{allocatedDensityLog B α O P})$, $C_M$ = `layerKernelIndexBound m M` $= M^{m 2^{m+1}}$, $T = \exp(\texttt{allocatedJetSupportLog B α O P})$, $\mathrm{residue}_j$ = the reduction modulo $\mathrm{modulus}$ of the integer matrix `allocatedNonkernelJetMatrix B U basis S x u rows j v₀` (`integerResidueMatrix`), and let $\mathrm{proxy}(z)$ be the mean, over $v$ drawn from the product over triples $j$ of `scalarCubeResidueWeights α (H j) modulus _ (fun _ => modulus) (r j) ...` (uniform cube weights on `IntegerScalarCubeBox α (H j)` conditioned on the residues $r_j$), of `allocatedNormalizedLongJetDensity B U basis S x u rows s hA` evaluated at the flattened parameter whose $(j, i)$ entry is $\bigl([i = \mathrm{none}]\, c(j) + \mathrm{step}(j)\, v_j(i)\bigr)/\ell_j$, and at $z$. If
--   $$\int \bigl| g(z) - \texttt{allocatedLongProfileDensity B U basis S x rows modulus residue proxy}\ z \bigr|\, d\lambda(z) \le E_{\mathrm{ref}},$$
--   then
--   $$\int \Bigl| \mathbb{E}_{v \sim \mathrm{law}}\, \texttt{allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1}\ z - g(z) \Bigr|\, d\lambda(z) \le (2T+1)^{N} \bigl( K\, \varepsilon\, (1 + C_M C + \varepsilon)^{K} \bigr) + E_{\mathrm{ref}},$$
--   where $N$ is the number of pairs $(a, o)$ with $a = (j, \cdot)$ an axis and $o \in O_j$, and $K$ is the number of non-grid axes.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSlicedLongJet_ideal_transfer_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSlicedLongJet_ideal_transfer` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedOriginalLongComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B194` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedOriginalLongComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSlicedLongJet_ideal_transfer)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

theorem allocatedSlicedLongJet_ideal_transfer_s2 {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hm : 0 < modulus) (r : tupleIndex → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize).weight v₀ ≠ 0)
    (g : AllocatedLongJetRows B U basis S O → ℝ)
    (hg : Integrable g (allocatedLongJetReference B U basis S O)) {Eref : ℝ} :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let law := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize
    let residue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    let proxy := fun z => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α
      (H j) modulus (hH j) (fun _ => modulus) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j))).mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (principalTupleFlatten activeB activeDegree α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / lengths j)) z)
    (∫ z, |g z - allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤ Eref →
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) - g z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) + Eref := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
