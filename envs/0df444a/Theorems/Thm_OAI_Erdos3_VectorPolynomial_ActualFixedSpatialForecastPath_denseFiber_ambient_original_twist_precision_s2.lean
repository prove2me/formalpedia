-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_denseFiber_ambient_original_twist_precision_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_original_twist_precision_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:55:54.431282+00:00
-- url     : https://prove2.me/theorems/a9ac1d19-a4cc-4ae9-8f3e-92332ebd6ec1
-- title:
--   On a dense fiber slice, the mean of a twist along the forecast path matches its box correlation with the early forecast target up to exp(-E)
-- statement:
--   This statement lives in a large context of data and structures defined by OpenAI; we follow the Lean `variable` declarations. Fix a natural number $m$ and a finite type $G$; for each $j < m$ finite types $I_j$, $J_j$, a natural number $n_j$, a real subspace $U_j$ of $\mathbb{R}^{J_j}$ with Euclidean subspace $V_j$, and a real basis $b_j$ of $V_j^{\perp}$ indexed by $\{0,\dots,n_j-1\}$ whose $\mathbb{Z}$-span is OpenAI's projected integer lattice of $V_j$; finite types $B_a$ for the layer sampler axes $a$; reals $R_j, \sigma_j$ with $R_j > 0$, $\sigma_j > 0$; a layer sampler scale $S$ (main field `S.value`); a finite type $X$ with decidable equality; finite types $E^{\mathrm{out}}_j$; natural numbers $D_{\mathrm{mod}}, L_{\mathrm{rank}}$ and embeddings `spatial`, `kernel`, `block`; a finite type $T_{\mathrm{sp}}$ with an equivalence $G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$; $\mathrm{physicalN} : X \to \mathbb{N}$ with $\mathrm{physicalN}_x > 0$ for all $x$; reals $\tau, \mathrm{cost}$; an `ActualFixedSpatialForecastSetup` $s$ (numerical fields including $s.D$, $s.P$, $s.P_{\mathrm{bad}}$, $s.P_\tau$, $s.\kappa$); sliced forecast numerics $q_{\mathrm{num}}, q_{\mathrm{Late}}$ for $s$ with equal fields $\delta$, Hchild, $v$, Ptail; reals $\delta_{\mathrm{base}}, P^{\mathrm{base}}_{\mathrm{pres}}$; an `ActualFixedSpatialForecastPath` `path` (with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, parameter `S.value`, $\mathrm{physicalN}$, $\tau$, $\delta_{\mathrm{base}}$, $s.P$, $s.P_{\mathrm{bad}}$, $P^{\mathrm{base}}_{\mathrm{pres}}$; it has fields including `noise`, `base`, `center`, `sample`, `read` and a reference modulus); and a dense slice input `input : ActualFixedSpatialDenseSliceInput s qnum` with `input.cost` $= \mathrm{cost}$. Fix orthonormal bases $o_j$ of $V_j$, $\mathbb{Z}$-bases $bW_j$ (indexed by $E^{\mathrm{out}}_j$) of the lattice sections $\Lambda_j = \mathbb{Z}^{J_j} \cap V_j$ (assumed to be $\mathbb{Z}$-lattices), left-invariant probability measures $\nu_j$ on $V_j/\Lambda_j$, and assume the product of these tori is compact.
--
--   Fix a twist $W$ (an OpenAI `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip`: a modulus $\le$ periodCap, a cover $\le$ coverCap, a mask bounded by $1$ and a Lip-Lipschitz smooth part bounded by $1$; `W.eval physicalN poly u` is OpenAI's evaluation of the twist), vector polynomials $\mathrm{originalpoly}_j$ in variables indexed by $X$ with coefficients in $U_j$ and of total degree at most $j+1$, and reals $\xi > 0$, $V$, $E$, $P_{\mathrm{test}}$, $R_{\mathrm{rank}}$, $C$, and a nonzero natural number $q$. Write $\Sigma$ = `s.slicedComparisonSourceLog P_test` and $\epsilon_m$ = `nativeForecastAmbientExponent m` (OpenAI). Assume:
--   - `path.noise` lies in OpenAI's `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths … τ ξ physicalN) 1`;
--   - $|\sigma_j| \le \exp\bigl(-\texttt{fixedPathSlicedPerturbationLog}\ s.D\ (s.D + \Sigma + 4)\ (\mathrm{cost} + 1)\ (2\Sigma + (E+4) + 14)\ m\bigr)$ for all $j$;
--   - the modulus and the cover of $W$ divide $q$, and $q$ divides the reference modulus of `path`;
--   - $2\lceil \tau\,\mathrm{physicalN}_i/4 \rceil \le \mathrm{physicalN}_i$ for all $i$, and `path.base` lies in the trimmed box $\{x : \lceil\tau\,\mathrm{physicalN}_i/4\rceil \le x_i < \mathrm{physicalN}_i - \lceil\tau\,\mathrm{physicalN}_i/4\rceil\}$;
--   - $s.\kappa$ equals OpenAI's `forecastGeometricJacobian` of $U$, $b$, $R$, `S.value`, the product of the basis axis scales $\lceil 1/\lVert b_j(i)\rVert\rceil$ over the short integer selection, and $\tau$;
--   - $0 \le P_{\mathrm{test}}$, $\mathrm{Lip} \le e^{P_{\mathrm{test}}}$, $\mathrm{periodCap} \le e^{P_{\mathrm{test}}}$, $\mathrm{coverCap} \le e^{P_{\mathrm{test}}}$;
--   - $0 \le q_{\mathrm{Late}}.\mathrm{massLog} + E + 8$; with $\Theta = \exp\bigl((\max(\max(s.P, 2\max(P_{\mathrm{test}}, 3q_{\mathrm{Late}}.\mathrm{Pnative} + 3) + 1), q_{\mathrm{Late}}.\mathrm{massLog} + E + 8) + \epsilon_m)^{\epsilon_m}\bigr)$: $\Theta \le \mathrm{physicalN}_i$ for all $i$ and $\Theta \le R_{\mathrm{rank}}$;
--   - `HasLayerSamplingRank (j+1) physicalN R_rank (U j) (originalpoly j)` for every $j$ (OpenAI: no nonzero integer row vector $a$ with entries bounded by $R_{\mathrm{rank}}$ and not orthogonal to $U_j$ makes the degree-$(j+1)$ homogeneous part of $a\cdot\mathrm{originalpoly}_j$ admit a rational approximation of OpenAI's kind);
--   - for some center on the coefficient torus and functions `sampleFn`, `readFn`: `AllocatedCenteredRecoveredSampleReadAt … C center path.center path.base sampleFn readFn` holds, `allocatedCenteredJointDensity … center path.base path.noise` $\ne 0$, `sampleFn path.noise = path.sample` and `readFn path.noise = path.read` (OpenAI);
--   - the integer box $\prod_x\{0,\dots,\mathrm{physicalN}_x - 1\}$ is nonempty; $0 \le \mathrm{cost}$, $0 \le E$, $\tau \le 1$, $q \le e^{V}$;
--   - `comparisonPrecisionFloor s (D_mod + Σ_j |I_j|) Σ V E` $\le$ `S.value`; $\xi \le \exp(-(2\Sigma + (E+4) + 14))$; $E + 8 \le q_{\mathrm{Late}}.E$; and $\exp\bigl(\texttt{forecastJointGridAmbientLog}\ (D_{\mathrm{mod}} + \sum_j |I_j|)\ (\texttt{comparisonGridLog}\ s\ \Sigma)\ (E+4)\ V\ s.P_\tau\bigr) \le \mathrm{physicalN}_i$ for all $i$ (OpenAI quantities);
--   - `earlyData` is an `ActualForecastData physicalN originalpoly earlyPnative earlyMassLog earlyCapLog earlyEdata` (OpenAI: a target function on the integer box together with finitely many twists and coefficients approximating it), with center constants equal to $j \mapsto$ `(path.center j).val` and target equal to the target of the slice of the dense slice member `path.toDenseSliceMember input` (built from the short integer selection, $o$, $bW$, $hb$, $\mathrm{originalpoly}$ and $s.\kappa$).
--
--   Then
--   $$\Bigl|\,\mathbb{E}_{z \sim \lambda}\, W.\mathrm{eval}\bigl(\mathrm{physicalN}, \mathrm{originalpoly}, \mathrm{path.base} + \mathrm{site}(z)\bigr) - \mathbb{E}_{u}\, W.\mathrm{eval}(\mathrm{physicalN}, \mathrm{originalpoly}, u)\cdot \mathrm{earlyData.target}(u)\Bigr| \le e^{-E},$$
--   where $\lambda$ = `input.box.fiberSliceLaw …` is the law on the integer box obtained by pushing the uniform distribution on the slice index set of the residue slice `input.box` forward to the box (the coordinates outside the slice fixed by `input.fixed`); $\mathrm{site}(z)$ = `integerPhysicalSite z path.noise` is the vector $a \mapsto \mathrm{noise}(\mathrm{none}, a) + \sum_{k} z_k\,\mathrm{noise}(k, a)$; and $u$ is uniform on the integer box.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_original_twist_precision_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_original_twist_precision` (in `lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_original_twist_precision)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable (qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
variable (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)
variable (hEarlyTarget : earlyData.target =
  (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
    s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget hδlate hHlate hvlate hTaillate in

theorem denseFiber_ambient_original_twist_precision_s2 :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by
  sorry

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
