-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_actualFixedSpatialSlicedForecastFamily_option_of_numerics
-- name    : OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastFamily_option_of_numerics
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:39:49.556002+00:00
-- url     : https://prove2.me/theorems/3fad156a-c277-432b-b590-6adb87d44f60
-- title:
--   Sliced forecast numerics give forecast data for each admissible path, zero data for none
-- statement:
--   Work in OpenAI's layer-sampler setting, with the following implicit: a natural number $m$; finite types $G$, $I_j$, $J_j$, $B_a$ and natural numbers $n_j$; subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $b_j$ of the orthogonal complements of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ (proofs $hR$, $h\sigma$) and a `LayerSamplerScale` $S$; a finite type $X$ with decidable equality; finite types $E^{\mathrm{out}}_j$; natural numbers $D_{\mathrm{mod}},L_{\mathrm{rank}}$; embeddings $\mathrm{spatial}$, $\mathrm{kernel}_j$, $\mathrm{block}_{j,a}$; a finite type $T_{\mathrm{sp}}$ with an equivalence $G\simeq X\oplus(X\oplus T_{\mathrm{sp}})$; reals $W_{\mathrm{sp}},L_{\mathrm{sp}}$; $\mathrm{physicalN}:X\to\mathbb{N}$; reals $\tau,\delta_{\mathrm{slice}}$; a finite type $A$ and $\mathrm{selected}:A\to\Sigma_j\,\mathrm{Fin}\,n_j$. Let $s$ be an `ActualFixedSpatialForecastSetup B U b S Dmod selected τ δslice` (a structure bundling numerical parameters with inequalities, including $s.\kappa$ and the fact `s.hBactive`), $q$ an `ActualFixedSpatialSlicedForecastNumerics s` (a structure bundling further numbers, including $P_{\mathrm{native}},\mathrm{massLog},\mathrm{capLog},E$), $o_j$ orthonormal bases of `euclideanSubspace (U j)`, $bW_j$ $\mathbb{Z}$-bases of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, $hb$ the hypothesis that the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`, and $\mathrm{originalpoly}_j$ vector polynomials on $X$ with values in $\mathbb{R}^{J_j}$ and coefficients in $U_j$ ($\mathrm{hmem}$). Let $\mathrm{Path}$ be the type `ActualFixedSpatialSlicedAdmissiblePath s q` (for these data; each element carries an `ActualFixedSpatialSlicedForecastPath` $\mathrm{path.slice}$). Then there is a map $\mathrm{data}$ assigning to each element of $\mathrm{Option}\ \mathrm{Path}$ an `ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E` (a structure bundling a complex target on `integerBox physicalN`, center constants, and a finite family of complex coefficients and normalized polynomial twists) such that: for every path, the target of $\mathrm{data}(\mathrm{some}\ \mathrm{path})$ is `path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ` and its center constants are $j\mapsto\mathrm{path.slice.path.center}_j$; $\mathrm{data}(\mathrm{none})$ has target $0$ and center constants $0$; for every $f$ and every $v$ in the box, $\|\mathrm{data}(f).\mathrm{target}(v)\|\le e^{q.\mathrm{capLog}}$; for every $f$, $\sum_i\|\mathrm{data}(f).\mathrm{coefficient}_i\|\le e^{q.\mathrm{massLog}}$; and for every $f$ and $v$,
--   $$\Big\|\mathrm{data}(f).\mathrm{target}(v)-\sum_i\mathrm{data}(f).\mathrm{coefficient}_i\cdot(\mathrm{data}(f).\mathrm{twists}_i).\mathrm{eval}\big(\mathrm{physicalN},\,j\mapsto\mathrm{originalpoly}_j-\mathrm{data}(f).\mathrm{centerConstant}_j,\,v\big)\Big\|\le e^{-q.E},$$
--   with "$-$ constant" being `subtractConstant`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastFamily_option_of_numerics` in `lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B079` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualSlicedForecastLateData.lean#L966

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B079

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

variable {Vact : Type*} [Fintype Vact] [DecidableEq Vact]
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "short" => allocatedShortAxis (I := I) U basis S.value

end Erdos3.VectorPolynomial

end

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))

namespace ActualFixedSpatialSlicedForecastPath

end ActualFixedSpatialSlicedForecastPath

end Erdos3.VectorPolynomial

end

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
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem exists_actualFixedSpatialSlicedForecastFamily_option_of_numerics :
    let Path := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q
    ∃ data : Option Path → ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E,
      (∀ path, (data (some path)).target =
        path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data (some path)).centerConstant = fun j => (path.slice.path.center j).val) ∧
      (data none).target = (fun _ => 0) ∧
      (data none).centerConstant = (fun _ _ => 0) ∧
      (∀ f v, ‖(data f).target v‖ ≤ Real.exp q.capLog) ∧
      (∀ f, (∑ i, ‖(data f).coefficient i‖) ≤ Real.exp q.massLog) ∧
      (∀ f v, ‖(data f).target v - ∑ i, (data f).coefficient i *
        ((data f).twists i).eval physicalN
          (fun j => subtractConstant ((data f).centerConstant j) (originalpoly j)) v.val‖ ≤
        Real.exp (-q.E)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
