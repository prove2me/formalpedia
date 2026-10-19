-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_relativePatchSliceConclusion_of_actual_retained_forecast_score_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_actual_retained_forecast_score_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:30:41.101736+00:00
-- url     : https://prove2.me/theorems/978791bc-eae4-4651-b574-66ef303fe463
-- title:
--   An actual retained forecast score on a sliced path gives a relative slice
-- statement:
--   Fix the data of OpenAI's actual fixed-spatial forecast setting: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$ for all $j$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); and reals $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$. Let `slice` be an `ActualFixedSpatialSlicedForecastPath` over these data (a structure bundling an `ActualFixedSpatialForecastPath` `slice.path` over the same data with a step $> 0$, kernel lengths and starts, principal lengths, steps and starts, and identities tying them to the path). Let $A$ be a finite type and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$; $hB$ a proof that $|B_a| \ge 4$ for every axis $a$ that is not short; $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ $\mathbb Z$-bases, indexed by $E_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $hb$ the statement that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; $d$ a natural number and $e : \mathrm{Fin}\,d \simeq \Sigma_j J_j$. Write $c_j$ for the vector of `slice.path.center j` and $\mathcal M =$ `slice.path.referenceRetainedCRTModulus cutoff` (a product of prime powers defined by OpenAI).
--
--   Assume $m > 0$ and $|X| + \sum_j (|E_j| + n_j) \le D_{\mathrm{mod}}$. Let `cutoff` be a natural number with $\mathrm{cutoff} > 0$ and $2/\mathrm{cutoff} \le 1/2$; $\kappa \ge 0$ real; $\mathrm{poly}_j$ vector polynomials on $X$ with values in $\mathbb R^{J_j}$ whose coefficients lie in $U_j$ (proof $hm$); and assume $N_i > 0$ for all $i$. Let $s, r, E', \mathrm{rankBound}$ be natural numbers; $w : \mathrm{Fin}\,r \to \mathbb N$ monotone with $1 \le w_j \le s$; $P^{\mathrm{sc}}_j \in \mathbb R[X]$ of degree at most $w_j$ (`weightedSupportLE 1 (w j)`); $p : \mathrm{Fin}\,d \to \mathbb N$; `Bpatch` a `WeightedParameterPatch (X ⊕ Fin d) (Sum.elim 1 p) s E'` (a structure of weights, weighted parameter slots and a `PatchKernel E'`); $\chi$ a `PatchKernel d` (a function $\mathbb R^d \to [0,1]$ supported where all $|x_i| \le 1/4$, Lipschitz with constant $\chi.\mathrm{lip}$); $M : \mathrm{Fin}\,d \times \mathrm{Fin}\,r \to \mathbb Z$ and $K \in \mathbb R_{\ge 0}$, with $\sum_j |M_{ij}| \le K$ for all $i$, $w_j \le p_i$ whenever $M_{ij} \ne 0$, and, for all $x : X \to \mathbb Z$, `fullTaggedBufferedCoordinates e poly c x` (the vector $i \mapsto \mathrm{poly}_{(e i).1}(x)_{(e i).2} - c_{e(i)}$) equal to $M$ applied to $(P^{\mathrm{sc}}_j(x))_j$. Let $\Lambda, L_{\mathrm{lift}}, C \in \mathbb R_{\ge 0}$ with $C \ge 1$, and write $\mathcal G(v, \rho, \beta, y) =$ `slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v ρ β y` ($\kappa$ times OpenAI's real function `retainedRecoveredG`, for $v : X \to \mathbb R$, $\rho : X \to \mathbb Z/\mathcal M$, $\beta : \mathrm{Fin}\,d \to \mathbb Z$, $y \in \mathbb R^d$). Assume: $v \mapsto \mathcal G(v, \rho, \beta, y)$ is $\Lambda$-Lipschitz for all $\rho, \beta, y$; $y \mapsto \mathcal G(v, \rho, \beta, y)$ is $L_{\mathrm{lift}}$-Lipschitz for all $v, \rho, \beta$; $\mathcal G$ takes values in $[0, C]$; and $\mathcal G(v, \rho, \mathrm{recoveredIntegerLift}(M, \beta, k)) = \mathcal G(v, \rho, \beta)$ for all $v, \rho, \beta, k$, where `recoveredIntegerLift M β k` $= \beta + Mk$. Let $f : (X \to \mathbb Z) \to \mathbb R$ take values in $[0,1]$ on `integerBox physicalN`, and $\lambda, \delta, \varepsilon, \mathrm{gain}, L'$ reals with $\lambda, \varepsilon \in [0,1]$, $\delta \ge 0$, $4/\mathrm{cutoff} \le \delta$, $(1+\delta)(1-\varepsilon) \le 1 - \delta$ and
--   $$\mathrm{gain} \le \mathop{\mathbb E}_{x \in \mathrm{integerBox\ physicalN}} \mathrm{Re}\bigl(\mathrm{slice.targetAt}(\mathrm{selected}, hB, o, bW, hb, \mathrm{poly}, hm, \kappa, x)\bigr) \cdot \mathrm{bufferedScalarScore}\bigl(\chi, y, T, f, \lambda, x\bigr),$$
--   where `targetAt` is a complex number defined by OpenAI ($\kappa$ times a `forecastLawDensityPhysicalTarget` built from the slice's data), $y(x) =$ `fullTaggedBufferedCoordinates e poly c x`, $T(u, \beta) =$ `Bpatch.value` at the point equal to $u$ on $X$ and $\beta$ on $\mathrm{Fin}\,d$, and `bufferedScalarScore χ y T f λ x` $= (f(x) - \lambda)\,\chi(y(x) - [y(x)])\, T(x, [y(x)])$ with $[\cdot]$ the coordinatewise nearest-integer lift. Assume finally $L' \ge 1$; $r, E', |X| \le L'$; $K, \Lambda, C, L_{\mathrm{lift}}, \chi.\mathrm{lip}$, `Bpatch.kernel.lip` and $\mathcal M$ are at most $e^{L'}$; $e^{-L'} \le \mathrm{gain}/(1+\delta)$; $\exp(\mathrm{spatialPatchExtractionCost}(L')) \le N_i$ for all $i$, where `spatialPatchExtractionCost L` $= 20(L+1)^2$; and $r + E' \le \mathrm{rankBound}$.
--
--   Then `RelativePatchSliceConclusion s physicalN f ((1 - ε) λ) rankBound (spatialPatchExtractionCost L')` holds: with $\Gamma = 20(L'+1)^2$, there exist $q > 0$, a `ResidueBoxSlice physicalN q` $S'$, a natural number $d'$ and a `PolynomialPatch X s d'` $A'$ such that every side length of $S'$ is at least $e^{-\Gamma} N_i$, $d' \le \mathrm{rankBound}$, `relativePatchComplexity A'` $\le \Gamma$, and $e^{-\Gamma} \le$ `relativePatchSliceScore S' f ((1 - ε) λ) A'`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_actual_retained_forecast_score_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_actual_retained_forecast_score` (in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B303`, `OAIE3v2B262` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_actual_retained_forecast_score)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B303
import Definitions.Def_OAIE3v2B262

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem relativePatchSliceConclusion_of_actual_retained_forecast_score_s2
    (hmpos : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (hN : ∀ i, 0 < physicalN i)
    {s r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (Λ Llift C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ residue β y, LipschitzWith Λ
      (fun v => slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y))
    (hGlift : ∀ v residue β, LipschitzWith Llift
      (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β))
    (hGcap : ∀ v residue β y,
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y ∈
        Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ v residue β k,
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue
        (recoveredIntegerLift M β k) =
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε gain L : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : gain ≤ 𝔼 x : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hL : 1 ≤ L) (hr : (r : ℝ) ≤ L) (hE : (E : ℝ) ≤ L)
    (hn : (Fintype.card X : ℝ) ≤ L)
    (hKbudget : (K : ℝ) ≤ Real.exp L) (hΛbudget : (Λ : ℝ) ≤ Real.exp L)
    (hCbudget : (C : ℝ) ≤ Real.exp L) (hLiftbudget : (Llift : ℝ) ≤ Real.exp L)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp L) (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp L)
    (hqbudget : (slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp L)
    (hgainBudget : Real.exp (-L) ≤ gain / (1 + δ))
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost L) ≤ (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion s physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost L) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
