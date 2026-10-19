-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_recentered_source_of_length_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_recentered_source_of_length_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:03.324208+00:00
-- url     : https://prove2.me/theorems/1f818b0d-1907-42f6-b2d5-b70138f017bd
-- title:
--   Under the allocated affine length condition, the recentered whole-law profile mean is bounded above by a residue-cell sum of the model, up to an explicit loss
-- statement:
--   All objects named in backticks are defined by OpenAI; hypothesis names in parentheses are those of the Lean statement.
--
--   **Context.** Let $m$ be a natural number, $G$ a finite type with decidable equality, $I_j$ ($j \in \operatorname{Fin} m$) finite types, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type with decidable equality to each axis of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $\mathrm{basis}_j$ a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ viewed in $\mathbb{R}^{J_j}$). Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$ (hR, hσ), and $S$ a `LayerSamplerScale B U basis R σ` with positive natural number `S.value`. Let $\mathrm{dim}$ be a natural number and $\mathrm{rowSets}_j$ a finite set of subsets of $\operatorname{Fin} \mathrm{dim}$ for each $j$; write $O_j$ for the type of members of $\mathrm{rowSets}_j$ and $\mathrm{rows}_j : O_j \to \operatorname{Finset}(\operatorname{Fin} \mathrm{dim})$ for the inclusion. Let $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value` and, for each $j$, an embedding $s_j$ of $O_j$ into `BoundedIntegerExponent G (j+1)`, such that the square submatrix of `scalarKernelIntegerJet x (j+1) rows_j` on the columns $s_j$ has nonzero determinant (hA). Let $M_k$ be a positive natural number (hMk) with `fixedKernelInverseBound S.positive x (j+1) rows_j (s j) (hA j) (1/Mk)` for each $j$ (hi: the inverse of the fixed pivot map has operator norm at most OpenAI's `kernelJetInverseAllowance`). Let $P \ge 0$ (hP) with $M_k \le e^P$ (hMkP), $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ (hRP, hRi, hσi), and $\#\,$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` $+ 1 \le e^P$ for each $j$ (hcount).
--
--   Write `grid` for the predicate `allocatedGridAxis U basis S.value` on axes (an axis $(j, \mathrm{inr}\ i)$ is a grid axis when `basisAxisScale (basis j) i` $\le \texttt{S.value}^{\texttt{layerTailDegree}\ m + 1}$; axes $(j, \mathrm{inl}\ \cdot)$ are not), `Tuple` for the index type of triples $(a, b, k)$ with $a$ a non-grid axis, $b \in B_a$ and $k \in \operatorname{Fin}(j+1)$ where $j$ is the degree index of $a$, and $L$ for the side lengths `allocatedPrincipalSides B U basis S` restricted to `Tuple`. Let $Q_j$ be finite types; assume the integer span of $\mathrm{basis}_j$ equals `projectedIntegerLattice (euclideanSubspace (U j))` (hb); let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$ and $bW_j$ a $\mathbb{Z}$-basis indexed by $Q_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the lattice $\mathbb{Z}^{J_j}$ intersected with `euclideanSubspace (U j)`); let $d$ be a positive natural number.
--
--   Let $H_0, \mathrm{step}_0$ be natural-number functions and $c_0$ an integer function on `PrincipalTupleIndex B (layerSamplerDegree I n)` (all triples $(a, b, k)$, grid or not), with $H_0 > 0$ (hH₀) and the progression `integerProgressionSupport (c₀ t) (step₀ t) (H₀ t)` (the set $\{c_0(t) + \mathrm{step}_0(t)\, i : 0 \le i < H_0(t)\}$) contained in $[0, \texttt{allocatedPrincipalSides B U basis S t})$ for each $t$ (hsubset₀). Let $\mathrm{modulus}$ be a natural number and $r_0$ assign to each triple $t$ and each $i \in \operatorname{Option}(\operatorname{Fin} \mathrm{dim})$ a residue in $\mathbb{Z}/\mathrm{modulus}$, such that the `principalTupleWeights B (layerSamplerDegree I n) H₀ hH₀` mass of the set of tuples $y$ with `principalResidueLabel modulus y` $= r_0$ is positive (hcell). Let `wholeLaw` be `containedSupportedProgressionLaw` built from these data and `gridLaw` the corresponding `containedSupportedProgressionAxisLaw` on the grid axes. For a principal integer tuple $y$ let `wholeRoot y` = `allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y` and `wholeDirs y` = `allocatedPhysicalCubeDirections B U basis S x y`.
--
--   Assume each such lattice section is a $\mathbb{Z}$-lattice; let $\nu_j$ be left-invariant probability measures on the tori `euclideanSubspace (U j)` modulo the lattice section, and `jetHaar` the product measure $\prod_j \prod_{O_j} \nu_j$ on `EuclideanJetLayers U O`. Assume `CoefficientTorus U` (for variables `LayerSamplerVariables G I n B`) is compact with a Borel measurable structure, and let $\mu$ be a left-invariant probability measure on it; write `density` for `allocatedCoefficientDensity B U basis hb o hR hσ S` and `cover` for `quotientIntegerCover (coefficientIntegerLattice U) d`. Let $X$ be a finite type with decidable equality. Assume also `CoefficientTorus U` for variables $\operatorname{Fin} \mathrm{dim}$ is compact with a Borel measurable structure, and let $\mu_{\mathrm{rows}}$ be a left-invariant probability measure on it (this measure is included in the statement but appears nowhere else).
--
--   **Hypotheses of the theorem.** Let $D, \mathrm{target}, P_k, P_\rho, F, T_{\mathrm{mod}}$ be real numbers with:
--   - (hdimensions) `AllocatedComparisonDimensions B (Fin dim) O D` (OpenAI's list of facts that $D \ge 0$ bounds $m$, $\#G$, $\mathrm{dim}$, the numbers of axes, triples, parameters, outputs, rows, coefficient exponents, and `probabilityProfileLipschitz`);
--   - $P_k \ge 0$, $M_k \le e^{P_k}$, $P_\rho \ge 0$, $\mathrm{target} \ge 0$, $F \ge 0$, $T_{\mathrm{mod}} \ge 0$;
--   - (hlength) $\exp(\texttt{allocatedAffineLengthLog m D P Prho Pk target F Tmod}) \le \texttt{S.value}$.
--
--   Let $g$ assign to each principal integer tuple $y$ (an element of `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S)`) a function $g_y$ on `EuclideanJetLayers U O` that is measurable (hgm), nonnegative (hg0) and `jetHaar`-integrable (hgi), such that (hglaw) the pushforward of the measure with density $z \mapsto \texttt{density}(\texttt{cover}\ z)$ with respect to $\mu$ under `euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows` equals the measure with density $g_y$ with respect to `jetHaar`. Let $\delta, \eta$ be reals, $\rho$ a function from predicates on axes to $\mathbb{R}_{\ge 0}$, $t \le 1$ (htone), and assume:
--   - (hs) `AllocatedAffineCoveredComparison B rows δ η ρ t htone` (an OpenAI proposition, universally quantified over all such data, asserting a covered comparison estimate);
--   - $0 < \rho(\texttt{grid}) \le 1$ (hρ, hρ1); $\sigma_j \le t$ for all $j$ (hσsmall);
--   - writing $H, \mathrm{step}, c$ for $H_0, \mathrm{step}_0, c_0$ restricted to `Tuple`: $\mathrm{step}(j) > 0$ (hstep); $\delta > 0$ and $\delta^{-1} \le e^F$ (hδ, hδF); $\delta L_j \le \#\,$`integerProgressionSupport (c j) (step j) (H j)` (hdense);
--   - $\mathrm{modulus} > 0$ (hm), $\mathrm{modulus} \le e^{T_{\mathrm{mod}}}$ (hmodulus);
--   - $\mathrm{selection} : \operatorname{Fin} \mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/Mk) Mk x` (hgood: the normalized scalar cube minor exceeds $1/M_k$ in absolute value and the column space of the cube difference matrix has bounded period $M_k$);
--   - $\mathrm{dim} \le m+1$ (hq); every row set in $\mathrm{rowSets}_j$ has at most $j+1$ elements (hrowDegree);
--   - (hperiod) for each $j$, the lattice $\mathrm{modulus} \cdot \mathbb{Z}^{O_j}$ is contained in the image of the integer matrix `scalarKernelIntegerJet x (j+1) rows_j`;
--   - $v_0$ is a principal axis tuple on the non-grid axes (`PrincipalAxisTuples`) whose weight under the first component law of `containedProgressionResidueLaw` (built from the `Tuple` data, `modulus`, the residues $r_0$ restricted to `Tuple`, and the readiness fact `allocatedAffineLength_slice_ready` derived from the hypotheses above) is nonzero (hv₀);
--   - $T : \operatorname{Fin} m \to \mathbb{R}$ with `partitionedIdealRadius (Fin dim) m` $+1 \le T_j$, where `partitionedIdealRadius α k` $= 1/4 + 2^{\#\alpha}(\#\alpha + 1)^k$ (hT), and $\#\,$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` $\cdot\, 2^{\mathrm{dim}} (\mathrm{dim}+1)^{j+1} \le T_j$ (hsource);
--   - $C : \operatorname{Fin} m \to \mathbb{R}$ with $C_j \ge 0$ (hC), $\|(\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)})^{-1} v\| \le C_j \|v\|$ for all $v$ (hchart), and $C_j \cdot (\#I_j + 1) \cdot T_j R_j \le 1/4$ (hbudget);
--   - $\rho(\texttt{grid})^{-1} \le e^{P_\rho}$ (hρlog); $0 \le \eta \le \exp(-(\mathrm{target} + 1 + D \cdot (m\, 2^{m+1}) P_k + 4))$ (hη0, hηsmall).
--
--   **Conclusion.** Let `center` and `width` be `principalProgressionSliceCenter` and `principalProgressionSliceWidth` of the `Tuple` progressions; let `ideal` be the `diagonalImageDensity`, with scale $R_j$ on the coordinate of a pair (non-grid axis of degree index $j$, row), of `activeAveragedSlicedProfileIdeal (G × Option (Fin dim)) (layerSamplerDegree I n) grid rows (ρ grid) center width`; and let `profile` $y$ be the `gridLaw`-mean over $u$ of `allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) modulus ideal y` (cast to $\mathbb{C}$). Then for every positive natural number $\mathrm{spatialModulus}$ and all $\mathrm{stride}, N : X \to \mathbb{N}$ the following holds, with $\mathrm{refined}$ = `residueRefinedPeriod spatialModulus stride` $= \mathrm{spatialModulus} \cdot \prod_x \mathrm{stride}(x)$ and labels the functions from triples and $\operatorname{Option}(\operatorname{Fin} \mathrm{dim})$ to $\mathbb{Z}/\mathrm{refined}$. Let $\mathrm{wholeReference}$ map labels to principal integer tuples, and let $r$ be a label such that every $y$ of nonzero `wholeLaw` weight has `principalResidueLabel refined y` $= r$, and `principalResidueLabel refined (wholeReference r)` $= r$. Let $W, \tau, \xi_n, \mathrm{mesh}$ be reals with $W \ge 0$; $\mathrm{base} : X \to \mathbb{Z}$; $\mathrm{cells}$ a finite set of column residue patterns on $\operatorname{Option}(\texttt{LayerSamplerVariables G I n B}) \times X$ modulo $\mathrm{stride}$; $\mathrm{poly}_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` of total degree at most $j+1$ (_hp) with all coefficients in $U_j$ (hmem); and $\mathrm{test} : (X \to (\mathrm{Unit} \sqcup \operatorname{Fin} \mathrm{dim}) \to \mathbb{Z}) \to \mathbb{C}$. Let `point` = `physicalCubeRowSample U d rows poly hmem`. Let $\mathrm{model}$ be a complex function on `EuclideanJetLayers U O` and $\kappa, \mathrm{loss}, \varepsilon_{\mathrm{trunc}}, P_{\mathrm{sample}}, R_{\mathrm{rank}}, S_{\mathrm{stride}}, \varepsilon_{\mathrm{sample}}, \eta_{\mathrm{sample}}, \delta_{\mathrm{sur}}$ reals. Assume:
--   - $\mathrm{stride}(i) > 0$ and $N(i) > 0$ for all $i$; $\tau > 0$; $\mathrm{mesh} > 0$; `allocatedPhysicalRootBudget B U basis S (fun _ => 0)` $\le W$;
--   - $\mathrm{spatialModulus} \cdot \mathbb{Z}^{\mathrm{Unit} \sqcup \operatorname{Fin} \mathrm{dim}}$ is contained in `pivotFullImage` of the `selectedSpatialPivot` and `selectedSpatialFreeColumns` of the vector $g \mapsto x(g)(\mathrm{none})$ and the matrix `scalarCubeDifferenceMatrix x` with respect to $\mathrm{selection}$;
--   - $\|\mathrm{test}(v)\| \le 1$ for all $v$;
--   - $\kappa \le \operatorname{Re}$ of the `wholeLaw` complex mean of `allocatedRecenteredProfileTerm B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test (fun y z => g y z)` (with parameters $\tau$ and $\xi = \xi_n$);
--   - $\varepsilon_{\mathrm{trunc}} \ge 0$ and $\|\mathrm{profile}(z) - \mathrm{model}(z)\| \le \varepsilon_{\mathrm{trunc}}$ for all $z$;
--   - $P_{\mathrm{sample}} \ge 0$, $\#X \le P_{\mathrm{sample}}$, $\#(\operatorname{Option}(\operatorname{Fin} \mathrm{dim}) \times X) \le P_{\mathrm{sample}}$, $d \le e^{P_{\mathrm{sample}}}$, $0 \le S_{\mathrm{stride}} \le e^{P_{\mathrm{sample}}}$, $\varepsilon_{\mathrm{sample}} > 0$, $1/\tau \le e^{P_{\mathrm{sample}}}$, $1/\varepsilon_{\mathrm{sample}} \le e^{P_{\mathrm{sample}}}$, $\mathrm{stride}(i) \le S_{\mathrm{stride}}$ for all $i$;
--   - with $A$ the natural number chosen (by `Classical.choose`) from OpenAI's theorem `exists_translated_physical_jet_l1_perturbation m dim`: $e^{(P_{\mathrm{sample}} + A)^A} \le N(i)$ for all $i$; `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)` for all $j$; $e^{(P_{\mathrm{sample}}+A)^A} \le R_{\mathrm{rank}}$;
--   - $\mathrm{actual}, \mathrm{surrogate}$ are complex functions on the torus `JetAmbientIndex O J → UnitAddCircle`, Lipschitz with constants $L_a, L_s \ge 0$ and bounded in norm by $C_a, C_s \ge 0$; $\eta_{\mathrm{sample}} > 0$; $\#\,$`CoefficientAmbientIndex (Fin dim) J` $\le P_{\mathrm{sample}}$; $L_a, L_s, C_a, C_s \le e^{P_{\mathrm{sample}}}$; $\sum_j \#\,$`BoundedCoefficientExponent (Fin dim) (j+1)` $\le e^{P_{\mathrm{sample}}}$; $\eta_{\mathrm{sample}}^{-1} \le e^{P_{\mathrm{sample}}}$;
--   - for all $y$: the `wholeLaw`-mean of $v \mapsto g_v(y)$ equals $\mathrm{actual}(\texttt{coveredJetAmbientTorus U 1 y})$, and $\|\mathrm{profile}(y) - \mathrm{surrogate}(\texttt{coveredJetAmbientTorus U 1 y})\| \le \delta_{\mathrm{sur}}$.
--
--   Now let `root` and `dirs` be `allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (wholeReference r)` and `allocatedPhysicalCubeDirections B U basis S x (wholeReference r)`; $H_{\mathrm{sp}}$ = `trimmedSpatialRootScale τ N stride`, i.e. $H_{\mathrm{sp}}(i) = \tau N(i)/8/\mathrm{stride}(i)$; $V$ = `narrowTrimmedSpatialWidths W τ ξn N`; $C_{\mathrm{sp}} = (\mathrm{spatialModulus}^{\mathrm{dim}+1} \cdot \texttt{anisotropicSpatialDensityCap selection (1/Mk)})^{\#X}$; and $\mathrm{volumeFactor} = (30/\psi(0))^{\#(\operatorname{Option}(\operatorname{Fin} \mathrm{dim}) \times X)} \cdot (((1+W)/\texttt{S.value})^{\mathrm{dim}})^{\#X}$, with $\psi$ = `smoothProbabilityProfile`. Assume further that $V(z) > 0$ for all $z$; that the (unconditional) sum over $z$ of `selectedResidueSmoothWeight stride cells V z` is positive; that $\sum_k |\texttt{physicalCubeCoefficient root dirs}_{i,k}| \le H_{\mathrm{sp}}(t)$ for all $t, i$; that $8 \cdot \texttt{probabilityProfileLipschitz} \le 20 H_{\mathrm{sp}}(t)$ and $1 \le H_{\mathrm{sp}}(t)$ for all $t$; and that
--   $$C_{\mathrm{sp}} \Bigl( \mathrm{volumeFactor} \cdot \bigl(e^{-\mathrm{target}} + 2\delta_{\mathrm{sur}} + (2\eta_{\mathrm{sample}} + \varepsilon_{\mathrm{sample}})\bigr) + 9^{\#(X \times (\mathrm{Unit} \sqcup \operatorname{Fin} \mathrm{dim}))} \bigl(((1+W)/\texttt{S.value})^{\mathrm{dim}}\bigr)^{\#X} \varepsilon_{\mathrm{trunc}} \Bigr) \le \mathrm{loss}.$$
--   Then
--   $$\kappa - \mathrm{loss} \le \operatorname{Re} \sum_{(c, w)} \texttt{selectedResidueCellWeight stride cells V c} \cdot \texttt{allocatedRecenteredResidueWeight}(\ldots, r, c, w) \cdot \mathrm{model}\bigl(\mathrm{point}(\texttt{allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r}\ c\ w)\bigr),$$
--   the sum running over $c \in \mathrm{cells}$ and $w \in$ `spatialWindow Hsp 4`, where `allocatedRecenteredResidueWeight` is taken with arguments $\tau$, $B, U, \mathrm{basis}, S, X, \mathrm{spatialModulus}, \mathrm{stride}, \mathrm{wholeReference}, x, \texttt{hMk}, \mathrm{selection}, \texttt{hgood}, N, \texttt{hW}, \mathrm{mesh}, \mathrm{base}, \mathrm{cells}, \mathrm{test}, r, c, w$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_recentered_source_of_length_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_recentered_source_of_length` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B235` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRecenteredSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_recentered_source_of_length)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B235

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ uX
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {dim : ℕ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset (Fin dim))).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset (Fin dim)) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
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

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

include μrows hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineIdeal_recentered_source_of_length_s2
    {D target Pk Prho F Tmod : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) jetHaar)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure jetHaar (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hmodulus : (modulus : ℝ) ≤ Real.exp Tmod)
    (selection : (Fin dim) ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card (Fin dim) ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := (Fin dim)) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue (allocatedAffineLength_slice_ready B U basis hdimensions hP hPrho hPk htarget hF hTmod S hlength H₀ step₀ c₀ hsubset₀ hδ hδF modulus hm hmodulus hstep hdense).2.1).weight v₀ ≠ 0)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))) :
    let center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option (Fin dim))
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let profile := fun y => ((gridLaw).mean (fun u =>
      allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ)
    ∀ (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ),
    let refined := residueRefinedPeriod spatialModulus stride
    let labels := PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined
    ∀ (wholeReference : labels → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
        (allocatedPrincipalSides B U basis S)) (r : labels),
    (∀ y, (wholeLaw).weight y ≠ 0 → principalResidueLabel refined y = r) →
    principalResidueLabel refined (wholeReference r) = r →
    ∀ {W τ ξn mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ),
    let point := physicalCubeRowSample U d rows poly hmem
    ∀ (model : EuclideanJetLayers U selectedRows → ℂ)
      {κ loss εtrunc Psample Rrank Sstride εsample ηsample δsur : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) →
    (∀ v, ‖test v‖ ≤ 1) →
    κ ≤ ((wholeLaw).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξn)
      B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test
      (fun y z => (g y z : ℂ)))).re →
    0 ≤ εtrunc → (∀ z, ‖profile z - model z‖ ≤ εtrunc) →
    0 ≤ Psample → (Fintype.card X : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psample →
    (d : ℝ) ≤ Real.exp Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,0} m dim)
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    ∀ (actual surrogate : (JetAmbientIndex selectedRows J → UnitAddCircle) → ℂ)
      (La Ls Ca Cs : ℝ≥0),
    LipschitzWith La actual → LipschitzWith Ls surrogate →
    (∀ z, ‖actual z‖ ≤ Ca) → (∀ z, ‖surrogate z‖ ≤ Cs) →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Psample →
    (La : ℝ) ≤ Real.exp Psample → (Ls : ℝ) ≤ Real.exp Psample →
    (Ca : ℝ) ≤ Real.exp Psample → (Cs : ℝ) ≤ Real.exp Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    (∀ y, ((wholeLaw).mean (fun v => g v y) : ℂ) = actual (coveredJetAmbientTorus U 1 y)) →
    (∀ y, ‖profile y - surrogate (coveredJetAmbientTorus U 1 y)‖ ≤ δsur) →
    let root := allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (wholeReference r)
    let dirs := allocatedPhysicalCubeDirections B U basis S x (wholeReference r)
    let Hsp := trimmedSpatialRootScale τ N stride
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    let Csp := ((spatialModulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (Mk : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root dirs i k : ℝ)|) ≤ Hsp t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hsp t) →
    (∀ t, 1 ≤ Hsp t) →
    Csp * (volumeFactor * (Real.exp (-target) + 2 * δsur + (2 * ηsample + εsample)) +
      ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
        (((1 + W) / S.value) ^ dim) ^ Fintype.card X) * εtrunc) ≤ loss →
    κ - loss ≤
      (∑ t : cells × spatialWindow (α := Fin dim) Hsp 4, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U basis S X spatialModulus stride wholeReference x hMk selection hgood
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
          t.1.val t.2.val))).re := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
