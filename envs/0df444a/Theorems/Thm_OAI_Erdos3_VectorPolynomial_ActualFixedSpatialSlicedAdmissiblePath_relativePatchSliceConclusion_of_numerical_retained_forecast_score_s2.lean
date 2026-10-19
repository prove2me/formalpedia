-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedAdmissiblePath_relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:10:07.09056+00:00
-- url     : https://prove2.me/theorems/57ad57e2-c5d5-4f82-b884-3f325a9d15ef
-- title:
--   A retained forecast score on an admissible sliced path gives a relative slice
-- statement:
--   Fix: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); reals $\tau, \delta_{\mathrm{slice}}$; a finite type $A$ and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$. Let $s$ be an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice` (over $X$ and $E$; a structure bundling inequalities and real parameters, among them $s.P, s.P_{\mathrm{bad}}, s.P_{\mathrm{pres}}, s.\kappa$ and a proof `s.hBactive` that $|B_a| \ge 4$ for every axis that is not short), `qnum` an `ActualFixedSpatialSlicedForecastNumerics s` (a structure of numerical parameters with inequalities, including reals `qnum.capLog` and `qnum.Pnative`), and `member` an `ActualFixedSpatialSlicedAdmissiblePath s qnum` over these data (a structure bundling an `ActualFixedSpatialSlicedForecastPath` `member.slice` with parameters $(s.P, s.P_{\mathrm{bad}}, s.P_{\mathrm{pres}})$ together with regularity, stride and kernel-width bounds in terms of `qnum`). Let $o_j$ be orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ $\mathbb Z$-bases, indexed by $E_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $hb$ the statement that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; $d$ a natural number and $e : \mathrm{Fin}\,d \simeq \Sigma_j J_j$. Write $c_j$ for the vector of `member.slice.path.center j` and $\mathcal M =$ `member.slice.path.referenceRetainedCRTModulus cutoff` (a product of prime powers defined by OpenAI).
--
--   Let `cutoff` be a natural number with $\mathrm{cutoff} > 0$ and $2/\mathrm{cutoff} \le 1/2$. Let $\mathrm{poly}_j$ be vector polynomials on $X$ with values in $\mathbb R^{J_j}$ whose coefficients lie in $U_j$ (proof $hm$). Let $\mathrm{degree}, r, E', \mathrm{rankBound}$ be natural numbers; $w : \mathrm{Fin}\,r \to \mathbb N$ monotone with $1 \le w_j \le \mathrm{degree}$; $P^{\mathrm{sc}}_j \in \mathbb R[X]$ ($j \in \mathrm{Fin}\,r$) of degree at most $w_j$ (`weightedSupportLE 1 (w j)`); $p : \mathrm{Fin}\,d \to \mathbb N$; `Bpatch` a `WeightedParameterPatch (X ⊕ Fin d) (Sum.elim 1 p) degree E'` (a structure of weights, weighted parameter slots and a `PatchKernel E'`); $\chi$ a `PatchKernel d` (a function $\mathbb R^d \to [0,1]$ supported where all $|x_i| \le 1/4$, Lipschitz with constant $\chi.\mathrm{lip}$); $M : \mathrm{Fin}\,d \times \mathrm{Fin}\,r \to \mathbb Z$ and $K \in \mathbb R_{\ge 0}$. Assume: $\sum_j |M_{ij}| \le K$ for all $i$; $w_j \le p_i$ whenever $M_{ij} \ne 0$; for all $x : X \to \mathbb Z$, `fullTaggedBufferedCoordinates e poly c x` (the vector $i \mapsto \mathrm{poly}_{(e i).1}(x)_{(e i).2} - c_{e(i)}$) equals $M$ applied to the vector $(P^{\mathrm{sc}}_j(x))_j$; for all $j$ and $a$, the integer vector $i \mapsto M_{e^{-1}\langle j, i\rangle, a}$ lies in `euclideanSubspace (U j)`; and $\mathcal M$ divides every $M_{ia}$. Let $f : (X \to \mathbb Z) \to \mathbb R$ take values in $[0,1]$ on `integerBox physicalN`, and let $\lambda, \delta, \varepsilon, \mathrm{score}, \mathrm{budget}$ be reals with $\lambda, \delta, \varepsilon \in [0,1]$, $4/\mathrm{cutoff} \le \delta$, $(1+\delta)(1-\varepsilon) \le 1 - \delta$, and
--   $$\frac{\mathrm{score}}{2} \le \mathop{\mathbb E}_{x \in \mathrm{integerBox\ physicalN}} \mathrm{Re}\bigl(\mathrm{member.slice.targetAt}(\mathrm{selected}, s.\mathrm{hBactive}, o, bW, hb, \mathrm{poly}, hm, s.\kappa, x)\bigr) \cdot \mathrm{bufferedScalarScore}\bigl(\chi, y, T, f, \lambda, x\bigr),$$
--   where `targetAt` is a complex number defined by OpenAI ($s.\kappa$ times a `forecastLawDensityPhysicalTarget` built from the slice's data), $y(x) =$ `fullTaggedBufferedCoordinates e poly c x`, $T(u, \beta) =$ `Bpatch.value` at the point equal to $u$ on $X$ and $\beta$ on $\mathrm{Fin}\,d$, and `bufferedScalarScore χ y T f λ x` $= (f(x) - \lambda)\,\chi\bigl(y(x) - [y(x)]\bigr)\, T\bigl(x, [y(x)]\bigr)$ with $[\cdot]$ the coordinatewise nearest-integer lift `nearestIntegerLift`. Assume further $\mathrm{budget} \ge 1$; $r, E', D_{\mathrm{mod}} \le \mathrm{budget}$; $K$, $\chi.\mathrm{lip}$, `Bpatch.kernel.lip` and $\mathcal M$ are at most $e^{\mathrm{budget}}$; `qnum.capLog` $\le \mathrm{budget}$ and `qnum.Pnative` $\le \mathrm{budget}$; $e^{-\mathrm{budget}} \le \mathrm{score}$; $\exp(\Gamma) \le N_i$ for all $i$, where $\Gamma =$ `spatialPatchExtractionCost (recoveredKernelScalarBudget budget)` $= 20\,(8(\mathrm{budget}+1)^2 + 1)^2$; and $r + E' \le \mathrm{rankBound}$.
--
--   Then `RelativePatchSliceConclusion degree physicalN f ((1 - ε) λ) rankBound Γ` holds: there exist $q > 0$, a `ResidueBoxSlice physicalN q` $S'$, a natural number $d'$ and a `PolynomialPatch X degree d'` $A'$ such that every side length of $S'$ is at least $e^{-\Gamma} N_i$, $d' \le \mathrm{rankBound}$, `relativePatchComplexity A'` $\le \Gamma$, and $e^{-\Gamma} \le$ `relativePatchSliceScore S' f ((1 - ε) λ) A'`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score` (in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialNumericalPatchEndpoint.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B252`, `OAIE3v2B262` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialNumericalPatchEndpoint.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252
import Definitions.Def_OAIE3v2B262

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
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
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    {degree r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ degree) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) degree E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (member.slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hr : (r : ℝ) ≤ budget) (hE : (E : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hKbudget : (K : ℝ) ≤ Real.exp budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hqbudget : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  sorry

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
end
