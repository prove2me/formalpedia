-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_toDenseSliceMember_nativeMean_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_nativeMean_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:57:04.381357+00:00
-- url     : https://prove2.me/theorems/836a5e12-675b-46ae-b0c5-48a44e92eb9f
-- title:
--   The native mean of a dense slice member is a fiber-slice mean of the twist
-- statement:
--   Work in OpenAI's layer-sampler setting, with all of the following implicit: a natural number $m$; finite types $G$, $I_j$, $J_j$ ($j<m$), $B_a$ (for $a$ in `LayerSamplerAxis I n`) and natural numbers $n_j$; subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $b_j$ of the orthogonal complements of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ and a `LayerSamplerScale` $S$; a finite type $X$ with decidable equality; finite types $E^{\mathrm{out}}_j$; natural numbers $D_{\mathrm{mod}},L_{\mathrm{rank}}$; embeddings $\mathrm{spatial}:\mathrm{Fin}\,L_{\mathrm{rank}}\hookrightarrow G$, $\mathrm{kernel}_j:\mathrm{Fin}\,L_{\mathrm{rank}}\times\mathrm{Fin}(j+1)\hookrightarrow G$ and $\mathrm{block}_{j,a}$ into the blocks of active axes; a type $T_{\mathrm{sp}}$ and an equivalence $G\simeq X\oplus(X\oplus T_{\mathrm{sp}})$; $\mathrm{physicalN}:X\to\mathbb{N}$; reals $\tau,\delta_{\mathrm{slice}},\delta_{\mathrm{base}},P_{\mathrm{presBase}}$; $s$ an `ActualFixedSpatialForecastSetup` (a structure bundling numerical parameters $D,P,P_{\mathrm{bad}},P_{\mathrm{pres}},\dots$ with inequalities among them) and $q$ an `ActualFixedSpatialSlicedForecastNumerics s` (a structure bundling further numbers such as $T,\delta,H_{\mathrm{child}},P_{\mathrm{tail}}$ with inequalities). Let $\mathrm{path}$ be an `ActualFixedSpatialForecastPath` for this data (with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, scale $S.\mathrm{value}$ and parameters $\tau,\delta_{\mathrm{base}},s.P,s.P_{\mathrm{bad}},P_{\mathrm{presBase}}$; a structure bundling an integer base point $\mathrm{base}:X\to\mathbb{Z}$, an integer noise array, a coefficient sample, centers $\mathrm{center}_j\in U_j$, a set of primes and further data), $\mathrm{input}$ an `ActualFixedSpatialDenseSliceInput s q` (a structure bundling a keep-predicate, a step, a `ResidueBoxSlice` $\mathrm{box}$ with positive lengths, fixed coordinates inside the box, and density inequalities), $W$ a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` (a structure bundling a modulus, a mask on $(\mathbb{Z}/\mathrm{modulus})^X$ and a bounded $\mathrm{Lip}$-Lipschitz smooth function), and $\mathrm{originalpoly}_j$ vector polynomials on $X$ with values in $\mathbb{R}^{J_j}$. Then the complex number `(path.toDenseSliceMember input).slice.nativeMean s W originalpoly` equals the mean, under the probability weights `input.box.fiberSliceLaw …` on `integerBox` (the push-forward of the uniform law on the slice's fiber parameters), of
--   $$z\mapsto W.\mathrm{eval}\ \mathrm{physicalN}\ (\mathrm{path.physicalPolynomial}\ \mathrm{originalpoly})\ \big(a\mapsto \mathrm{path.base}(a)+\text{integerPhysicalSite}(z,\mathrm{path.noise})(a)\big),$$
--   where `path.physicalPolynomial originalpoly` subtracts the constant $\mathrm{path.center}_j$ from $\mathrm{originalpoly}_j$ and `integerPhysicalSite root w` is $i\mapsto w(\mathrm{none},i)+\sum_k \mathrm{root}_k\,w(\mathrm{some}\,k,i)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_nativeMean_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_nativeMean` (in `lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B248`, `OAIE3v2B252` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_nativeMean)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B252

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
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
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ δslice δbase PpresBase : ℝ}
variable {s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice}
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ)
  physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

omit [Fintype Tsp] in
theorem toDenseSliceMember_nativeMean_s2 :
    (path.toDenseSliceMember input).slice.nativeMean s W originalpoly =
      (input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) := by
  sorry

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
