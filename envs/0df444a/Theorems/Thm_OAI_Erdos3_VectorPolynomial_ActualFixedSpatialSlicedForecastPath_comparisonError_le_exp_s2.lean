-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_comparisonError_le_exp_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonError_le_exp_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:56:34.939975+00:00
-- url     : https://prove2.me/theorems/7163724f-53f8-4a09-84d2-b1a1afe2c62e
-- title:
--   The sliced forecast comparison error is at most e^(-E) above the precision floor
-- statement:
--   Work in OpenAI's layer-sampler setting, with the following implicit: a natural number $m$; finite types $G$, $I_j$, $J_j$, $B_a$ and natural numbers $n_j$; subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $b_j$ of the orthogonal complements of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ (proofs $hR$, $h\sigma$) and a `LayerSamplerScale` $S$; a finite type $X$ with decidable equality; finite types $E^{\mathrm{out}}_j$; natural numbers $D_{\mathrm{mod}},L_{\mathrm{rank}}$; embeddings $\mathrm{spatial}$, $\mathrm{kernel}_j$, $\mathrm{block}_{j,a}$; a finite type $T_{\mathrm{sp}}$ with an equivalence $G\simeq X\oplus(X\oplus T_{\mathrm{sp}})$; $\mathrm{physicalN}:X\to\mathbb{N}$; and reals $\tau,\mathrm{cost}$. Let $s$ be an `ActualFixedSpatialForecastSetup` for this data with selection `allocatedShortIntegerSelection U b S.value`, tolerance $\tau$ and slice width $e^{-\mathrm{cost}}/2$ (a structure bundling numerical parameters $D,P,L,P_{\mathrm{bad}},P_{\mathrm{pres}},P_K,\dots$ with inequalities), and let $\mathrm{slice}$ be an `ActualFixedSpatialSlicedForecastPath` over it (with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, scale $S.\mathrm{value}$ and parameters $\tau,e^{-\mathrm{cost}}/2,s.P,s.P_{\mathrm{bad}},s.P_{\mathrm{pres}}$; a structure bundling an `ActualFixedSpatialForecastPath`, a step, and kernel and principal progression lengths and starts). Let $o_j$ be orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$, $\mathrm{Lip}\ge0$ and $P_u,V,E,E_{\mathrm{data}},Q,\xi,M_{\mathrm{mass}}$ real numbers. Assume $\mathrm{cost}\ge0$, $P_u\ge2$, $E\ge0$, $s.D^2\le P_u$, $s.L\le e^{P_u}$, $\tau\le1$, $\mathrm{Lip}\le e^{P_u}$; let $q$ be a nonzero natural number with $q\le e^{V}$; assume `comparisonPrecisionFloor s (Dmod + |Σ j, I j|) Pu V E` $\le S.\mathrm{value}$ (a natural number defined by OpenAI); assume $e^{-\mathrm{cost}}S.\mathrm{value}\le$ `slice.principalLength` at every principal index over a non-short axis, and $e^{-\mathrm{cost}}S.\mathrm{value}\le$ `slice.kernelLength g` for every $g$; $0\le\xi\le e^{-(2P_u+(E+4)+14)}$; $M_{\mathrm{mass}}\le e^{Q}$; and $E+8\le E_{\mathrm{data}}$. Set $d=D_{\mathrm{mod}}+|\Sigma_j I_j|$, $F=2P_u+(E+4)+14$, $\eta=e^{-F}$, $t=e^{-\phi}$ with $\phi$ = `fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) F m`, and $P_g$ = `comparisonGridLog s Pu`. Then `slice.comparisonError` (a real number defined by OpenAI as a sum of a sliced physical comparison error, $2\delta_{\mathrm{native}}+M\,e^{-E_{\mathrm{prec}}}$ and an ambient grid error), taken with Lipschitz bound $\mathrm{Lip}$, $\xi$, $t$, $\delta=e^{-\mathrm{cost}}$, $\varepsilon=2e^{\mathrm{cost}}/S.\mathrm{value}$, $\eta$, $q$, $o$, $\delta_{\mathrm{native}}=e^{-E_{\mathrm{data}}}$, $M=M_{\mathrm{mass}}$, $E_{\mathrm{prec}}=Q+E+8$, cutoff `forecastJointGridCutoff Pg (E + 4)` ($=\lceil e^{P_g+E+8}\rceil$) and mesh `forecastJointGridMesh d Pg (E + 4)`, is at most $e^{-E}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonError_le_exp_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonError_le_exp` (in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedModelPrecision.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B252` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedModelPrecision.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonError_le_exp)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252

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
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

theorem comparisonError_le_exp_s2
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Lip : ℝ≥0} {Pu V E Edata Q ξ Mmass : ℝ}
    (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
    (hDsq : s.D * s.D ≤ Pu) (hAL : (s.L : ℝ) ≤ Real.exp Pu)
    (hτ1 : τ ≤ 1) (hLip : (Lip : ℝ) ≤ Real.exp Pu)
    (q : ℕ) [NeZero q] (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) Pu V E ≤ S.value)
    (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
    (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ))
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ Real.exp (-(2 * Pu + (E + 4) + 14)))
    (hM : Mmass ≤ Real.exp Q) (hEdata : E + 8 ≤ Edata) :
    let d := Dmod + Fintype.card (Σ j, I j)
    let F := 2 * Pu + (E + 4) + 14
    let η := Real.exp (-F)
    let t := Real.exp (-fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) F m)
    let Pg := comparisonGridLog s Pu
    slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := Real.exp (-cost))
      (ε := 2 * Real.exp cost / S.value) (η := η) (q := q) (hδ := Real.exp_pos _)
      (o := o) (δnative := Real.exp (-Edata)) (M := Mmass) (Eprec := Q + E + 8)
      (cutoff := forecastJointGridCutoff Pg (E + 4))
      (δgrid := forecastJointGridMesh d Pg (E + 4)) ≤ Real.exp (-E) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
