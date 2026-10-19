-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedAdmissiblePath_relativePatchSliceConclusion_of_prepared_shear_score_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_prepared_shear_score_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:34:50.441986+00:00
-- url     : https://prove2.me/theorems/796c7ef1-863b-4871-8ea2-0920b8803f64
-- title:
--   A prepared shear-orbit score on an admissible sliced path gives a relative slice
-- statement:
--   Fix: a finite type $X$ with decidable equality, a type $J_0$, a natural number $m$ and a `RankPreparationFamily X J₀ m` `prep` (a family of $m$ rank-preparation layers; layer $j$ carries a finite coordinate type $\mathrm{Coord}_j$, a real subspace $\mathrm{space}_j \le \mathbb R^{\mathrm{Coord}_j}$ of dimension `rank`, and a vector polynomial $\mathrm{poly}_j$ on $X$ with values in $\mathbb R^{\mathrm{Coord}_j}$); write $U_j = \mathrm{space}_j$. Fix further a finite type $G$; finite types $I_j$ and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, $\mathrm{short} =$ `allocatedShortAxis U b S.value`); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); reals $\tau, \delta_{\mathrm{slice}}$; a finite type $A$ and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$. Let `setup` be an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice` (over $X$ and $E$; a structure bundling inequalities and real parameters, among them $\kappa =$ `setup.κ` and a proof `setup.hBactive` that $|B_a| \ge 4$ for every axis that is not short), `qnum` an `ActualFixedSpatialSlicedForecastNumerics setup` (numerical parameters with inequalities, including reals `qnum.capLog` and `qnum.Pnative`), and `member` an `ActualFixedSpatialSlicedAdmissiblePath setup qnum` over these data (a structure bundling an `ActualFixedSpatialSlicedForecastPath` `member.slice` with regularity, stride and kernel-width bounds). Let $o_j$ be orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ $\mathbb Z$-bases, indexed by $E_j$, of `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace (U j))`; $hb$ the statement that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; and $e : \mathrm{Fin}(\mathrm{tagCount}) \simeq$ `prep.PreparedCoordinate` $= \Sigma_j \mathrm{Coord}_j$. Write $c_j$ for the vector of `member.slice.path.center j` and $\mathcal M =$ `member.slice.path.referenceRetainedCRTModulus cutoff` (a product of prime powers defined by OpenAI).
--
--   Let $P_{\mathrm{prep}}, q_{\mathrm{log}}$ be reals and $R_{\mathrm{prep}}$ a natural number with `prep.PreparedHeights Pprep Rprep` (every layer $i$ is `Valid` at degree $i+1$ with height `preparationHeight Pprep (m - 1 - i)` and bound $R_{\mathrm{prep}}$; its second component gives that the coefficients of $\mathrm{poly}_j$ lie in $U_j$), $P_{\mathrm{prep}} \ge 0$, $R_{\mathrm{prep}} \ge 1$, $|\mathrm{Coord}_j| \le P_{\mathrm{prep}}$ for all $j$, and $\|bW_j(a)\| \le \exp((P_{\mathrm{prep}} + 2)^{\mathrm{preparedIntegralBasisExponent}(m)})$ for all $j, a$ (`preparedIntegralBasisExponent` is a natural-number function of $m$ defined by OpenAI). Let `cutoff` be a natural number with $\mathrm{cutoff} > 0$ and $2/\mathrm{cutoff} \le 1/2$, with $\mathcal M \le e^{q_{\mathrm{log}}}$. Let $\mathrm{degree}, d_0, \mathrm{old}, \mathrm{removed}, \mathrm{returned}$ be natural numbers with $m \le \mathrm{degree}$, $\sum_j \mathrm{rank}_j \le m \cdot \mathrm{removed}$, $\mathrm{removed} \le \mathrm{old}$ and $\mathrm{returned} \le d_0 + \mathrm{degree}\,(\mathrm{old} - \mathrm{removed})$. Let `patch` be a `PolynomialPatch Y degree returned` for some type $Y$; let `ambient` be a polynomial orbit (`PolynomialOrbit`) of the realification of `polynomialShearFiltration patch.weight degree _` with weights `fullTaggedVariableWeight Coord` ($1$ on $X$ and $j+1$ on $\mathrm{Coord}_j$); and let $\mathrm{patchCost}$ be real with `relativePatchComplexity patch` $\le \mathrm{patchCost}$. Let $f : (X \to \mathbb Z) \to \mathbb R$ take values in $[0,1]$ on `integerBox physicalN`, and $\lambda, \delta, \varepsilon, \mathrm{score}, \mathrm{budget}$ reals with $\lambda, \delta, \varepsilon \in [0,1]$, $4/\mathrm{cutoff} \le \delta$, $(1+\delta)(1-\varepsilon) \le 1 - \delta$, and
--   $$\frac{\mathrm{score}}{2} \le \mathop{\mathbb E}_{x \in \mathrm{integerBox\ physicalN}} \mathrm{Re}\bigl(\mathrm{member.slice.targetAt}(\mathrm{selected}, \mathrm{setup.hBactive}, o, bW, hb, \mathrm{poly}, \_, \kappa, x)\bigr) \cdot \mathrm{bufferedScalarScore}\bigl(\chi, y, T, f, \lambda, x\bigr),$$
--   where `targetAt` is a complex number defined by OpenAI ($\kappa$ times a `forecastLawDensityPhysicalTarget` built from the slice's data), $\chi =$ `majorPhasePlateauKernel tagCount` (the patch kernel $x \mapsto$ `linearCutoff (1/8) (1/8) ‖x‖`, of Lipschitz constant $8$), $y(x) =$ `fullTaggedBufferedCoordinates e poly c x` (the vector $i \mapsto \mathrm{poly}_{(e i).1}(x)_{(e i).2} - c_{e(i)}$), $T(u, \beta)$ is the value of the `WeightedParameterPatch` `patch.ofTaggedWeightedShearOrbit e ambient` at the point equal to $u$ on $X$ and $\beta$ on $\mathrm{Fin}(\mathrm{tagCount})$, and `bufferedScalarScore χ y T f λ x` $= (f(x) - \lambda)\,\chi(y(x) - [y(x)])\, T(x, [y(x)])$ with $[\cdot]$ the coordinatewise nearest-integer lift. Assume further $\mathrm{budget} \ge 1$; $d_0 + \mathrm{degree} \cdot \mathrm{old} \le \mathrm{budget}$; $D_{\mathrm{mod}} \le \mathrm{budget}$; $q_{\mathrm{log}} + (P_{\mathrm{prep}} + 2)^{\mathrm{preparedIntegralBasisExponent}(m) + 1} \le \mathrm{budget}$; $\mathrm{patchCost} \le \mathrm{budget}$; `qnum.capLog` $\le \mathrm{budget}$; `qnum.Pnative` $\le \mathrm{budget}$; $e^{-\mathrm{budget}} \le \mathrm{score}$; and $\exp(\Gamma) \le N_i$ for all $i$, where $\Gamma =$ `spatialPatchExtractionCost (recoveredKernelScalarBudget budget)` $= 20\,(8(\mathrm{budget}+1)^2 + 1)^2$.
--
--   Then `RelativePatchSliceConclusion degree physicalN f ((1 - ε) λ) (d₀ + degree · old) Γ` holds: there exist $q > 0$, a `ResidueBoxSlice physicalN q` $S'$, a natural number $d'$ and a `PolynomialPatch X degree d'` $A'$ such that every side length of $S'$ is at least $e^{-\Gamma} N_i$, $d' \le d_0 + \mathrm{degree} \cdot \mathrm{old}$, `relativePatchComplexity A'` $\le \Gamma$, and $e^{-\Gamma} \le$ `relativePatchSliceScore S' f ((1 - ε) λ) A'`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_prepared_shear_score_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_prepared_shear_score` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedActualShearPatchEndpoint.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B262`, `OAIE3v2B264` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedActualShearPatchEndpoint.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_prepared_shear_score)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B262
import Definitions.Def_OAIE3v2B264

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {X J₀ : Type} [Fintype X] [DecidableEq X]
variable {m : ℕ} (prep : RankPreparationFamily X J₀ m)
variable {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics setup)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) setup qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)

theorem relativePatchSliceConclusion_of_prepared_shear_score_s2
    {preparationP qLog : ℝ} {Rprep : ℕ}
    (hprep : prep.PreparedHeights preparationP Rprep)
    (hp : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (hqLog : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp qLog)
    {degree d₀ old removed returned : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : returned ≤ d₀ + degree * (old - removed))
    {Y : Type*} (patch : PolynomialPatch Y degree returned)
    (ambient : (polynomialShearFiltration patch.weight degree patch.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord)))
    {patchCost : ℝ} (hPatchCost : relativePatchComplexity patch ≤ patchCost)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) (fun j => (hprep j).2.1) setup.κ x.val).re *
        bufferedScalarScore (majorPhasePlateauKernel tagCount)
          (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
            (fun j => (member.slice.path.center j).val))
          (fun u β => (patch.ofTaggedWeightedShearOrbit e ambient).value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : qLog + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : patchCost ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ)) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  sorry

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
end
