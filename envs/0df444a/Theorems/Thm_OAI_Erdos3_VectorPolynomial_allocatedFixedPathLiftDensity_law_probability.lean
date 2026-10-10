-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathLiftDensity_law_probability
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPathLiftDensity_law_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:09:15.423928+00:00
-- url     : https://prove2.me/theorems/11962810-93f7-46b6-bdab-ebcb2e254bca
-- title:
--   The allocated fixed-path lift map pushes the unit box to a probability density
-- statement:
--   The statement uses these section variables. Let $m \in \mathbb{N}$, $G$ a finite type, $I_j$ ($j \in \mathrm{Fin}\ m$) finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B_a$ finite types with decidable equality indexed by $a \in$ `LayerSamplerAxis I n` $= \Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$, $P$ a decidable predicate on axes, and $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$. Write $\deg$ = `layerSamplerDegree I n` ($\deg(j, \cdot) = j+1$), call an axis active if $\neg P(a)$, let $\mathrm{Coeff}$ = `ActiveProfileCoefficientIndex G B deg P` (OpenAI's index type of sampler coefficient slots on the active axes), $\mathrm{Input} = \Sigma_{a \text{ active}}\, B_a \times \mathrm{Fin}(\deg a)$ and $\mathrm{Output}$ = $\Sigma_{a \text{ active}}\,\mathrm{Unit}$. Assume $R_j \ne 0$ for all $j$ and $|B_a| \ge 4$ for every active $a$. Let $\mathrm{lower}, \mathrm{width} : \forall a \text{ active}, B_a \times \mathrm{Fin}(\deg a) \to \mathbb{R}$, and let $a, \delta$ be reals with $a > 0$, $\delta > 0$, $a \le$ `unitProfilePrincipalSize` of every active axis (an explicit positive real depending on $|B_j|$), $\delta \le \mathrm{width}_j(p)$ and $0 \le \mathrm{lower}_j(p)$ for all $j, p$. Let $r : \mathrm{Coeff} \to \mathbb{R}$ with $|r_e| \le 1$ for all $e$. Let $F$ = `allocatedFixedPathLiftMap B P R σ lower width r` $: \mathbb{R}^{\mathrm{Input}} \to \mathbb{R}^{\mathrm{Output}}$ (OpenAI's shift plus joint sliced principal map) and $f$ = `allocatedFixedPathLiftDensity B P R σ hB lower width r` $: \mathbb{R}^{\mathrm{Output}} \to \mathbb{R}$. Then the push-forward under $F$ of `unitBoxMeasure Input` (Lebesgue measure restricted to OpenAI's positive unit box in $\mathbb{R}^{\mathrm{Input}}$) equals the measure with density $f$ with respect to Lebesgue measure; $f \ge 0$ everywhere; $f$ is integrable; and $\int f = 1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPathLiftDensity_law_probability` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedSlicedIdealDensity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B142` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedSlicedIdealDensity.lean#L224

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B170

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
variable (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

theorem allocatedFixedPathLiftDensity_law_probability
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) :
    (unitBoxMeasure Input).map (allocatedFixedPathLiftMap B P R σ lower width r) =
        realDensityMeasure volume (allocatedFixedPathLiftDensity B P R σ hB lower width r) ∧
      (∀ y, 0 ≤ allocatedFixedPathLiftDensity B P R σ hB lower width r y) ∧
      Integrable (allocatedFixedPathLiftDensity B P R σ hB lower width r) ∧
      (∫ y, allocatedFixedPathLiftDensity B P R σ hB lower width r y) = 1 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
