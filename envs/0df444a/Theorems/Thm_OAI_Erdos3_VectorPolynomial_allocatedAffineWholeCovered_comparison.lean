-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineWholeCovered_comparison
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineWholeCovered_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:08:09.034075+00:00
-- url     : https://prove2.me/theorems/4154626d-f0f6-4552-897f-1c97daf7c513
-- title:
--   Whole-progression covered expectation compared with the grid-averaged profile integral
-- statement:
--   Fix the section data. A natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$, natural numbers $n_j$, finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$ (in a universe $u_J$), real subspaces $U_j \subseteq \mathbb R^{J_j}$, bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of $V_j = $ `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$, $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ` with value $L_S = $ `S.value`; a finite type $\alpha$ with decidable equality; finite types $O_j$ with decidable equality and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; a point $x : G \to $ `IntegerScalarCubeBox α L_S`; embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` (exponents of total degree $\le j+1$) such that the square integer matrices obtained by restricting the columns of `scalarKernelIntegerJet x (j+1) (rows j)` to $s_j$ have nonzero determinant ($hA$); a positive natural number $M_k$ with `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/Mk)` for all $j$ (a bound on the norm of an inverse pivot map, defined by OpenAI); a real $P \ge 0$ with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$; finite types $Q_j$ (in a universe $u_Q$); the hypothesis $hb$ that the $\mathbb Z$-span of `basis j` is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$, indexed by $Q_j$, of the lattice $\mathbb Z^{J_j} \cap V_j$; a positive natural number $d$; a function $F$ from `AllocatedFrozenCoefficients B U basis S` $\times$ `EuclideanJetLayers U O` to $\mathbb C$; natural-valued $H_0, \mathrm{step}_0$ and integer-valued $c_0$ on `PrincipalTupleIndex B (layerSamplerDegree I n)`, with $H_0 > 0$ and each progression $\{c_0(t) + \mathrm{step}_0(t)\,k : 0 \le k < H_0(t)\}$ contained in $[0, \texttt{allocatedPrincipalSides B U basis S t})$; a natural number $\mathrm{modulus}$ and residues $r_0(t, i) \in \mathbb Z/\mathrm{modulus}$; and the hypothesis $hcell$ that the set of tuples whose residue label (`principalResidueLabel modulus`) equals $r_0$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀`.
--
--   Write grid for the predicate `allocatedGridAxis U basis L_S` on axes, Tuple for the principal tuple index over the non-grid axes, $L$ for `principalAxisLength (¬ grid) (allocatedPrincipalSides B U basis S)` on Tuple, and $H, \mathrm{step}, c, \mathrm{residue}$ for the restrictions of $H_0, \mathrm{step}_0, c_0, r_0$ to Tuple. Let actual be `allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d F H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell` (a complex number defined by OpenAI) and gridLaw the probability weights `containedSupportedProgressionAxisLaw … grid` on the grid tuples `PrincipalAxisTuples grid (allocatedPrincipalSides B U basis S)`.
--
--   Let $\delta, \eta$ be reals, $\rho$ a function from predicates on axes to $\mathbb R_{\ge 0}$, $t \le 1$, and assume: `AllocatedAffineCoveredComparison B rows δ η ρ t htone` (a proposition defined by OpenAI); $\sigma_j \le t$ for all $j$; $\mathrm{step}_j > 0$ and $H_j \ge 2$ for $j \in$ Tuple; $\delta > 0$; $\delta L_j \le |\{c_j + \mathrm{step}_j k : 0 \le k < H_j\}|$; $\mathrm{modulus} > 0$; $(|\alpha| + 1)\,\mathrm{modulus} \le H_j$; `scalarCubeGridBoundaryConstant α` $\cdot\,\mathrm{modulus}/H_j$ is less than the Lebesgue measure of `scalarCubeDomain α`; $\varepsilon \ge 0$ with $\mathrm{step}_j/L_j \le \varepsilon$; an embedding $\mathrm{selection} : \alpha \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x`; $|\alpha| \le m + 1$; reals $e \ge 0$ and $\varepsilon_{\mathrm{coef}} > 0$ with $\varepsilon_{\mathrm{coef}}^{-1} \le \exp(e)$; $\exp(\texttt{allocatedKernelReplacementLog B α O P e}) \le L_S$; for every $j$, the lattice $\mathrm{modulus}\cdot\mathbb Z^{O_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)`; a tuple $v_0$ in `PrincipalAxisTuples (¬ grid) (allocatedPrincipalSides B U basis S)` of nonzero weight under `containedProgressionResidueLaw … L H step c … modulus hm residue hsize`; reals $\mathrm{mesh} \in [0,1]$ with $1/L_S^{\,\texttt{layerTailDegree}\ m + 1} \le \mathrm{mesh}$ and $C_{\mathrm{mask}} \ge 1$ such that, for every grid tuple $u$, every $j$ and $z$, the value of `allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue u j) z` lies in $[0, C_{\mathrm{mask}}]$, where `outputResidue u j` is `integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus`; and $F$ is measurable with $\|F\| \le 1$.
--
--   Let ideal be `diagonalImageDensity (o ↦ R_{o}) (activeAveragedSlicedProfileIdeal … grid rows (ρ grid) center width)`, with center and width given by `principalProgressionSliceCenter … L c` and `principalProgressionSliceWidth … L H step`. Then
--   $$\Bigl\|\mathrm{actual} - \sum_u \mathrm{gridLaw}(u) \int\!\!\int \texttt{allocatedLongProfileDensity}(\dots, \mathrm{outputResidue}\,u, \mathrm{ideal})(z)\cdot\texttt{allocatedCoveredFixedTest}(\dots, u, v_0, \dots, F)(a_0, z)\Bigr\|$$
--   (inner integral in $z$ against `allocatedLongJetReference B U basis S O`, outer in $a_0$ against `allocatedFrozenCoefficientSource B U basis hR hσ S`) is at most
--   $$\bigl(2e^{\Lambda_J} + 1\bigr)^{|\Sigma_a O_a|}\, N\,\varepsilon_{\mathrm{coef}} \bigl(1 + \kappa\,e^{\Lambda_D} + \varepsilon_{\mathrm{coef}}\bigr)^{N} + \texttt{allocatedAffineSourceReferenceError B U basis S α O (ρ grid) P η (fun \_ => modulus) H ε mesh Cmask},$$
--   where $\Lambda_J = $ `allocatedJetSupportLog B α O P`, $\Lambda_D = $ `allocatedDensityLog B α O P`, $\kappa = $ `layerKernelIndexBound m Mk` $= M_k^{\,m\,2^{m+1}}$, $N$ is the number of non-grid axes, and $|\Sigma_a O_a|$ is the number of pairs of an axis $a$ and an element of $O$ at its layer.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineWholeCovered_comparison` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean#L941

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "proxyRadius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "Outputs" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d F
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineWholeCovered_comparison
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (_ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, O a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ‖actual - FiniteProbabilityWeights.complexMean gridLaw (fun u => ∫ a₀, ∫ z,
      (allocatedLongProfileDensity B U basis S x rows modulus (outputResidue u) ideal z : ℂ) *
        allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d F a₀ z
      ∂reference ∂frozenSource)‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α O (ρ grid) P η (fun _ => modulus) H ε mesh Cmask
 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
