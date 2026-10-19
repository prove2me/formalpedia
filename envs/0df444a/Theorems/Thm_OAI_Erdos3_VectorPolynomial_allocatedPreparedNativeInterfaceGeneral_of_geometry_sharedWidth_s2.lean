-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:16:13.187574+00:00
-- url     : https://prove2.me/theorems/d8d1affe-0954-4287-a415-804522fde059
-- title:
--   Early native source geometry yields the shared-width prepared native interface
-- statement:
--   Fix the data of OpenAI's allocated layer-sampler setup (all types in universe $0$): a natural number $m$; finite types $G$ (with decidable equality), $I_j$, $J_j$, $Q_j$ ($j < m$), and $B(a)$ for each layer-sampler axis $a$; dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0, \dots, n_j - 1\}$) of the orthogonal complement of $U_j$ with $hb$: the $\mathbb{Z}$-span of `basis j` equals `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ (indexed by $I_j$) of $U_j$; $\mathbb{Z}$-bases $bW_j$ (indexed by $Q_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, assumed to be a $\mathbb{Z}$-lattice in $U_j$; reals $R_j > 0$ and $\sigma_j > 0$; a `LayerSamplerScale B U basis R σ` $S$; natural numbers $s$ and $n_X$; an embedding `selection` $: \{0, \dots, s\} \hookrightarrow G$; functions $\mathrm{stride}, N : \{0, \dots, n_X - 1\} \to \mathbb{N}$ with every $N(i) \ne 0$; a polynomial $P_{\mathrm{detect}}$ with natural-number coefficients; reals $p_{\mathrm{detect}}, q_{\mathrm{detect}}, \alpha, P$; left-invariant probability measures $\nu_j$ on the tori $U_j / \texttt{latticeSection}$; left-invariant probability measures $\mu$ on `CoefficientTorus (K := LayerSamplerVariables G I n B) U` and $\mu_{\mathrm{rows}}$ on `CoefficientTorus (K := Fin (s + 1)) U` (each torus given as a compact space with a Borel measurable structure); and a Borel measurable structure on `SiteTorus (Finset (Fin (s + 1))) U`. (The data $hb$, $o$, $bW$, $\mu$, $\nu$, $\mu_{\mathrm{rows}}$, $hR$, $h\sigma$ are included in the statement.)
--
--   Assume $s \le m$. Let $P_{\mathrm{chart}}, D, \mathrm{target}, P_k, P_\rho, Q_{\mathrm{stride}}$ be reals and $K \in \mathbb{R}_{\ge 0}$, and suppose given `geometry` of type `AllocatedEarlyNativeSourceGeometryGeneral Pchart P D target Pk Prho Qstride pDetect K` (an OpenAI structure, for these $s$, $B$, $U$, `basis`, $S$, $n_X$, bundling quantitative hypotheses such as $P \ge 0$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, counting bounds and chart bounds).
--
--   Then `AllocatedPreparedNativeInterfaceGeneralSharedWidth Pchart P D target Pk Prho Qstride K` holds, for the data $B$, $U$, `basis`, $hR$, $h\sigma$, $S$, `selection`, `stride`, $N$, $P_{\mathrm{detect}}$, $p_{\mathrm{detect}}$, $q_{\mathrm{detect}}$, $\alpha$, $Q$, $hb$, $o$ above. This is a proposition defined by OpenAI; it begins by assuming that the detected kernel cutoff `allocatedDetectedKernelCutoff s G |LayerSamplerVariables G I n B| Pdetect pDetect qDetect α` is at most $e^P$ and at most $e^{P_k}$, that $Q_{\mathrm{stride}} \ge 0$, and that every $\mathrm{stride}(i)$ is positive and at most $e^{Q_{\mathrm{stride}}}$, and under further hypotheses asserts the prepared native interface estimate with a shared width.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth` (in `lean/OAI/Combinatorics/Progressions/Estimates/SharedWidthPreparedModularGeneralDirectDetectionFreeTrim.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B284` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SharedWidthPreparedModularGeneralDirectDetectionFreeTrim.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B284

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include hb o bW μ ν μrows hR hσ in

theorem allocatedPreparedNativeInterfaceGeneral_of_geometry_sharedWidth_s2
    (hsm : s ≤ m)
    (Pchart D target Pk Prho Qstride : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K) :
    AllocatedPreparedNativeInterfaceGeneralSharedWidth (B := B) (U := U) (basis := basis)
      (hR := hR) (hσ := hσ) (S := S) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (pDetect := pDetect) (qDetect := qDetect) (α := α)
      (Q := Q) (hb := hb) (o := o) Pchart P D target Pk Prho Qstride K := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
