-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteScheduleGeometryDirectSource_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleGeometryDirectSource_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:23:38.312962+00:00
-- url     : https://prove2.me/theorems/0c7f3d7f-6282-4db7-89bf-d800023476cf
-- title:
--   Prepared scalar bounds and geometry give scheduled direct source availability
-- statement:
--   Fix: natural numbers $m, s$; a finite type $G$ with decidable equality; finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$ and finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$ with proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$; a `LayerSamplerScale` $S$ for $(B, U, \mathrm{basis}, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a natural number $n_X$; an embedding $\mathrm{selection} : \mathrm{Fin}(s+1) \hookrightarrow G$; $\mathrm{stride}, N : \mathrm{Fin}\,n_X \to \mathbb N$; a polynomial $P_{\mathrm{detect}} \in \mathbb N[x]$; reals $u_{\mathrm{src}}, p_{\mathrm{model}}, p_{\mathrm{slice}}$ (`sourceU`, `pModel`, `pSlice`); $V_{\mathrm{tail}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$; a real $\tau$; a proof $hb$ that the $\mathbb Z$-span of $\mathrm{basis}_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; finite types $Q_j$ and $\mathbb Z$-bases $bW_j$, indexed by $Q_j$, of the lattice sections `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (assumed `IsZLattice`); left-invariant probability measures $\nu_j$ on the quotients of `euclideanSubspace (U j)` by these sections; and a compact Borel structure with a left-invariant probability measure $\mu$ on `CoefficientTorus (K := LayerSamplerVariables G I n B) U`.
--
--   Let $C_{\mathrm{detect}}$ be a natural number equal to `sampledSupportedSlicedDetectionConstant s Pdetect`, and assume $s \le m$. Let $P_{\mathrm{chart}}, P_{\mathrm{scale}}, D, \mathrm{target}, P_k, P_\rho, Q_{\mathrm{stride}}, P_{\mathrm{master}}, P_{\mathrm{late}}, p_{\mathrm{gain}}, P_{\mathrm{phys}}, \mathrm{coarseTarget}, p_{\mathrm{radius}}$ be reals such that
--   `PreparedUniformDegreeDirectScalarBounds m s nX |LayerSamplerVariables G I n B| Cdetect Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius sourceU pModel pSlice` holds (a structure of OpenAI bundling inequalities among these reals, e.g. $0 \le P_{\mathrm{master}} \le P_{\mathrm{late}}$, $P_{\mathrm{chart}}, D, p_{\mathrm{radius}} \le P_{\mathrm{master}}$, $p_{\mathrm{slice}} \le p_{\mathrm{model}}$, $p_{\mathrm{gain}} + 32 \le \mathrm{coarseTarget} \le P_{\mathrm{late}}$, and more), and `PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius (2 sourceU + 4 pModel + 7) pGain` holds (a geometric condition defined by OpenAI; `allocatedModelTestLog u p` $= 2u + 5p + 12$). Assume further $R_j \le 1$ and $R_j^{-1} \le e^{p_{\mathrm{radius}}}$ for all $j$; $\sigma_j \le 1$ for all $j$; $S.\mathrm{value} \le e^{P_{\mathrm{late}}}$; for all $j$ and $i \in \mathrm{Fin}(n_j)$, with $r_j = |$`boundedBooleanJetRows (Fin (s+1)) (j+1)`$|$, both `positiveModerateSpectrumBlockCount j r_j ((layerTailDegree m + 1) r_j)` and `uniformSpectrumBlockCount j r_j ((j+1) r_j)` are at most $|B_{\langle j, \mathrm{inr}\, i\rangle}|$; and $(s+1)(s+3) \le |G|$.
--
--   Then `PreparedScheduledDirectSourceAvailability` holds for these data and the reals $P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}, P_{\mathrm{late}}, p_{\mathrm{gain}}, P_{\mathrm{phys}}, \mathrm{coarseTarget}$: for every real $\alpha$ with $e^{-(2u_{\mathrm{src}} + 4p_{\mathrm{model}} + 7)} \le \alpha \le 1$, the proposition `PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface` (an interface of OpenAI asserting a native-twist detection conclusion under budget hypotheses, with parameters $u = u_{\mathrm{src}}$, $p_{\mathrm{model}}$, $p_{\mathrm{slice}}$, $\alpha$, $\tau$ and the data above) holds.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleGeometryDirectSource_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleGeometryDirectSource` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleCandidateDetection.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B285` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleCandidateDetection.lean (declaration OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleGeometryDirectSource)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section General

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (sourceU pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include ν bW μ in

theorem preparedFiniteScheduleGeometryDirectSource_s2
    (Cdetect : ℕ) (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G) :
    PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  sorry

end General

end Erdos3.VectorPolynomial

end

end OAI
end
