-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_kernel_residue_riemann
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_kernel_residue_riemann
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T16:52:49.339185+00:00
-- url     : https://prove2.me/theorems/a7ca1bee-4434-4549-9bc8-0894d9864545
-- title:
--   Riemann-sum comparison for fixed-path sliced kernel averages along residue progressions
-- statement:
--   The statement uses these section variables (the hypotheses $hR$, $hσ$ are omitted). Let $m \in \mathbb{N}$, $G$ a finite type with decidable equality, $X$ a finite type, $I_j, J_j$ ($j \in \mathrm{Fin}\ m$) finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B_a$ finite types indexed by $a \in$ `LayerSamplerAxis I n` $= \Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$, $U_j \subseteq \mathbb{R}^{J_j}$ real subspaces, $\mathrm{basis}_j$ a real basis of the orthogonal complement of `euclideanSubspace (U j)` indexed by $\mathrm{Fin}(n_j)$, $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$, and $S$ a `LayerSamplerScale B U basis R σ` (OpenAI's structure: a positive natural number $S.\mathrm{value}$ with width and gap conditions). Call an axis $a$ short if `allocatedShortAxis U basis S.value a` and active otherwise; write $\deg$ = `layerSamplerDegree I n`, $\mathrm{Input} = \Sigma_{a \text{ active}} B_a \times \mathrm{Fin}(\deg a)$, $\mathrm{Output} = \Sigma_{a \text{ active}} \mathrm{Unit}$, $\mathrm{Sample}$ = `CoefficientSamplerArrays I n` over `LayerSamplerVariables G I n B`, and $\mathrm{Domain} = \mathbb{R}^{\Sigma_{x \in X} (\mathrm{Unit} \oplus \mathrm{Empty})} \times \mathbb{R}^{\mathrm{Output}}$. Let $W$ = `allocatedPhysicalRootBudget B U basis S (fun _ => 0)` (here $|$`LayerSamplerVariables G I n B`$| \cdot S.\mathrm{value}$), and for $t \in \mathbb{R}^G$ let $\Phi(t)$ = `fixedSpatialKernelMap W S.value z t`, the map $(x, \cdot) \mapsto z(\mathrm{none}, x) + \frac{S.\mathrm{value}}{1+W}\sum_g z(\mathrm{some}\ g, x)\,t_g$. Let $\Psi(v)$ = `allocatedOriginalSampleLiftMap B U basis S lower width sample v` (OpenAI's shift plus joint sliced principal map $\mathbb{R}^{\mathrm{Input}} \to \mathbb{R}^{\mathrm{Output}}$).
--
--   Now let $z : \mathrm{Option}\ G \times X \to \mathbb{R}$ with $|z(\mathrm{some}\ g, x)| \le 1$ for all $g, x$; $\mathrm{sample} \in \mathrm{Sample}$; $\mathrm{lower}, \mathrm{width} : \forall a \text{ active}, B_a \times \mathrm{Fin}(\deg a) \to \mathbb{R}$; $H : G \to \mathbb{N}$ with all $H_g > 0$; $\mathrm{start} : G \to \mathbb{Z}$; $\mathrm{step} > 0$ natural with each progression $\{\mathrm{start}_g + \mathrm{step}\cdot k : 0 \le k < H_g\}$ (`integerProgressionSupport`) contained in $[0, S.\mathrm{value})$; $q$ a positive natural with $q \le H_g$ and $c_0 \cdot q/H_g < 1$ for all $g$, where $c_0$ = `scalarCubeGridBoundaryConstant Empty` (an explicit constant); and $\varphi : (G \to \mathbb{Z}/q) \to \mathrm{Domain} \to \mathbb{C}$ with every $\varphi(r)$ $K_\varphi$-Lipschitz and $|\varphi(r)(y)| \le 1$. Let $\mathbb{E}_x$ denote the mean with respect to the product over $g$ of the probability weights `integerScalarCubeWeights Empty (H g)` on a single integer coordinate $x_g$ (uniform weights conditioned on OpenAI's `IntegerScalarCube (H g)` set), $\mathbb{E}_r$ the uniform mean over $r \in (\mathbb{Z}/q)^G$, and $\int dv$, $\int dk$ integrals against Lebesgue measure restricted to the positive unit boxes $(0,1]^{\mathrm{Input}}$ and $(0,1]^G$. Then
--   $$\Bigl|\mathbb{E}_x \int \varphi\bigl(\mathrm{start} + \mathrm{step}\cdot x \bmod q\bigr)\Bigl(\Phi\bigl(\tfrac{\mathrm{start} + \mathrm{step}\cdot x}{S.\mathrm{value}}\bigr), \Psi(v)\Bigr)dv - \mathbb{E}_r \int\!\!\int \varphi\bigl(\mathrm{start} + \mathrm{step}\cdot r\bigr)\Bigl(\Phi\bigl(\tfrac{\mathrm{start} + \mathrm{step}(H-1)k}{S.\mathrm{value}}\bigr), \Psi(v)\Bigr)dv\,dk\Bigr| \le \bigl(1 + 2(2c_0 + K_\varphi) + K_\varphi\bigr)\sum_g \frac{q}{H_g},$$
--   with all operations on $G$-indexed vectors taken coordinatewise.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_kernel_residue_riemann` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedFixedPathSlicedKernelResidueRiemann.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B135`, `OAIErdos3B141` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedFixedPathSlicedKernelResidueRiemann.lean#L619

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135
import Definitions.Def_OAIErdos3B141

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

omit hR hσ in
theorem allocatedFixedPath_sliced_kernel_residue_riemann
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (sample : Sample)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (H : G → ℕ) (hH : ∀ g, 0 < H g) (start : G → ℤ)
    (step : ℕ) (hstep : 0 < step)
    (hcontained : ∀ g, integerProgressionSupport (start g) (step : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (q : ℕ) [NeZero q] (hsize : ∀ g, q ≤ H g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H g) < 1)
    (φ : (G → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (H g) (hH g))).complexMean
        (fun x => ∫ v, φ (fun g => ((start g + (step : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((start g : ℝ) + (step : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input) -
      (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun r =>
        ∫ k, ∫ v, φ (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
          ∂unitBoxMeasure Input ∂unitBoxMeasure G)‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) *
        ∑ g, (q : ℝ) / H g := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
