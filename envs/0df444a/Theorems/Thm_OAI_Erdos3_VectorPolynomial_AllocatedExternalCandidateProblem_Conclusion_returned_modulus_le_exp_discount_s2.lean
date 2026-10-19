-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_returned_modulus_le_exp_discount_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.returned_modulus_le_exp_discount_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:48:27.701841+00:00
-- url     : https://prove2.me/theorems/d63dbea4-6208-4f7d-9e57-04967320b370
-- title:
--   The retained CRT modulus returned by an allocated external candidate conclusion is at most exp(2048 budget^3)
-- statement:
--   This statement lives in a large context of data and structures defined by OpenAI; we list it in the order of the Lean `variable` declarations. Fix a natural number $m$ and finite types $G$, $X$ (and a type $J_0$); a rank preparation family `prep : RankPreparationFamily X J₀ m` (for each $j < m$ a subspace `(prep j).space`, coordinates and a polynomial) with prepared heights `hprep : prep.PreparedHeights preparationP Rprep`; finite types $I_j$, $E^{\mathrm{out}}_j$, natural numbers $n_j$, finite types $B_a$ for the layer sampler axes $a$; bases $b_j$ of the orthogonal complements of the Euclidean subspaces of `(prep j).space` with $\mathbb{Z}$-span equal to the projected integer lattice; positive reals $R_j, \sigma_j$; a layer sampler scale $S$ (with value `S.value`); natural numbers $D_{\mathrm{mod}}$, $L_{\mathrm{rank}}$; embeddings `spatial`, `kernel`, `block` into $G$ and into the $B$'s; a type $T_{\mathrm{sp}}$ (not assumed finite) with an equivalence $G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$; $N : X \to \mathbb{N}$; reals $\tau, \xi, \mathrm{cost}$; an `ActualFixedSpatialForecastSetup` $s$ (with forecast parameters at $e^{-\mathrm{cost}}/2$; among its numerical fields are the reals $s.P$, $s.P_{\mathrm{bad}}$, $s.P_{\mathrm{pres}}$); sliced forecast numerics `qnum : ActualFixedSpatialSlicedForecastNumerics s` (with fields including the natural number `qnum.Hchild` and the reals `qnum.δ`, `qnum.v`, `qnum.Ptail`); orthonormal bases $o_j$ of the Euclidean subspaces of `(prep j).space`; the assumption that each lattice section $\mathbb{Z}^{\mathrm{Coord}_j} \cap$ (Euclidean subspace of `(prep j).space`) is a $\mathbb{Z}$-lattice; strides $X \to \mathbb{N}$, a finite set of column residue cells and a center on the coefficient torus; an `AllocatedExternalCandidateSampler` $A$ (with sides `A.sides k`); a type $Y$, a rational Lie algebra $M$, natural numbers $\mathrm{degree}, d, t$, a polynomial patch `patch : PolynomialPatch Y degree d`, a nilpotent filtration $F_{\mathrm{mark}}$ of $M$ of step $t$, a Lie homomorphism $\varphi$ from the polynomial shear Lie algebra of the patch weights to $M$, and a marked polynomial orbit; a function $f : \mathbb{Z}^X \to \mathbb{R}$ and $\lambda \in \mathbb{R}$; reals chartCost, massThreshold, scoreThreshold, outputMass, outputScore; an `AllocatedExternalCandidateProblem` $\mathcal{P}$ for $A$, the polynomial shear nilmanifold of the patch, $F_{\mathrm{mark}}$, $\varphi$, the marked orbit, the observable $z \mapsto$ `patch.shearObservable z` and the function $x \mapsto f(x) - \lambda$; a conclusion `out : 𝒫.Conclusion cost outputMass outputScore` (OpenAI structure with a set `out.retained` of retained points); reals $\delta_{\mathrm{base}}$, $P^{\mathrm{base}}_{\mathrm{pres}}$; and for each retained $z$ an `ActualFixedSpatialForecastPath` `path z` (with the data above, root budget `allocatedPhysicalRootBudget … (fun _ => 0)`, parameters `S.value`, $N$, $\tau$, $\delta_{\mathrm{base}}$, $s.P$, $s.P_{\mathrm{bad}}$, $P^{\mathrm{base}}_{\mathrm{pres}}$).
--
--   Assume the hypotheses from this context that the statement uses:
--   - for every retained $z$ and every $k$, the chart of $\mathcal{P}$ at $z$ keeps $k$ if and only if `qnum.Hchild` $\le$ `A.sides k`;
--   - $G$ is nonempty; `qnum.Hchild` $\le$ `S.value`; $2 \le e^{-\mathrm{cost}}\cdot$`S.value`;
--   - `qnum.δ` $\le e^{-\mathrm{cost}}$; $\mathrm{cost} + 1 \le$ `qnum.v`; $\mathrm{cost} + 1 \le s.P_{\mathrm{pres}}$; $2e^{\mathrm{cost}} \le$ `qnum.Ptail`.
--
--   For a retained $z$, these hypotheses give (via OpenAI's `out.denseSliceInput s qnum z …`, using the common tuple of `path z`) a dense slice input, and `ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)` is the resulting dense slice member, whose slice carries a forecast path written $\mathrm{path}'_z$ = `(member z).slice.path` (a reparameterization of `path z`). For a cutoff $c \in \mathbb{N}$, `referenceRetainedCRTModulus c` of a path is the product of $p^{e(p)}$ over its reference retained primes $p$ (its primes $p$ with nonzero reference bad depth, or nonzero prescribed exponent, or $p \le c$), where $e$ is the exponent function of the path; and `retainedPatchCutoff ε` $= \lceil 16/\varepsilon \rceil$ (natural-number ceiling), both defined by OpenAI.
--
--   Now let $\varepsilon, \mathrm{budget}, P_{\mathrm{test}}$ be real numbers with $0 < \varepsilon \le 1$, $1 \le \mathrm{budget}$, $\varepsilon^{-1} \le \mathrm{budget}$, and $P_{\mathrm{test}}, s.P_{\mathrm{bad}}, s.P_{\mathrm{pres}} \in [0, \mathrm{budget}]$. Assume that for every retained $z$ the exponent function of `path z` is $p \mapsto \lfloor \log_p \lceil e^{2P_{\mathrm{test}}} \rceil \rfloor$ (Lean's `Nat.log`, with the natural-number ceiling). Then for every retained $z$,
--   $$\texttt{referenceRetainedCRTModulus}\ (\texttt{retainedPatchCutoff}\ \varepsilon) \text{ of } \mathrm{path}'_z \;\le\; \exp\bigl(2048\,\mathrm{budget}^3\bigr).$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.returned_modulus_le_exp_discount_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.returned_modulus_le_exp_discount` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedExternalCandidateReturnedModulusBudget.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B248`, `OAIE3v2B252` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedExternalCandidateReturnedModulusBudget.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.returned_modulus_le_exp_discount)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B252

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord))}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
local notation "member" z => ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)

omit [Fintype Tsp] in

theorem returned_modulus_le_exp_discount_s2
    {ε budget Ptest : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hbudget : 1 ≤ budget) (hinv : ε⁻¹ ≤ budget)
    (htest : Ptest ∈ Set.Icc 0 budget)
    (hbad : s.Pbad ∈ Set.Icc 0 budget) (hpres : s.Ppres ∈ Set.Icc 0 budget)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (z : out.retained) :
    ((member z).slice.path.referenceRetainedCRTModulus (retainedPatchCutoff ε) : ℝ) ≤
      Real.exp (2048 * budget ^ 3) := by
  sorry

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end
