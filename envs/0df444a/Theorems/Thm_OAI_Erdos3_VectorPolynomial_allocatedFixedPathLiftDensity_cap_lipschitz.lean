-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathLiftDensity_cap_lipschitz
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPathLiftDensity_cap_lipschitz
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T21:37:32.699408+00:00
-- url     : https://prove2.me/theorems/6a02d461-18a8-4d6d-bb08-2ca702f89267
-- title:
--   The allocated fixed-path lift density is capped and Lipschitz
-- statement:
--   The statement uses these section variables. Let $m \in \mathbb{N}$, $G$ a finite type, $I_j$ ($j \in \mathrm{Fin}\ m$) finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B_a$ finite types with decidable equality indexed by $a \in$ `LayerSamplerAxis I n` $= \Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$, $P$ a decidable predicate on axes, and $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$. Write $\deg$ = `layerSamplerDegree I n` ($\deg(j, \cdot) = j+1$), call an axis active if $\neg P(a)$, let $\mathrm{Coeff}$ = `ActiveProfileCoefficientIndex G B deg P` (OpenAI's index type of sampler coefficient slots on the active axes) and $\mathrm{Output}$ = $\Sigma_{a \text{ active}}\,\mathrm{Unit}$. Assume $R_j \ne 0$ for all $j$ and $|B_a| \ge 4$ for every active $a$. Let $\mathrm{lower}, \mathrm{width} : \forall a \text{ active}, B_a \times \mathrm{Fin}(\deg a) \to \mathbb{R}$, and let $a, \delta$ be reals with $a > 0$, $\delta > 0$, $a \le$ `unitProfilePrincipalSize` of every active axis (an explicit positive real depending on $|B_j|$), $\delta \le \mathrm{width}_j(p)$ and $0 \le \mathrm{lower}_j(p)$ for all $j, p$. Let $r : \mathrm{Coeff} \to \mathbb{R}$ with $|r_e| \le 1$ for all $e$. Let $K_j$ = `allocatedFixedPathLiftRowCap P ha hδ j` $\in \mathbb{R}_{\ge 0}$ for each active axis $j$ (an explicit cap of OpenAI depending on $a$, $\delta$ and $\deg j$), and $f$ = `allocatedFixedPathLiftDensity B P R σ hB lower width r` $: \mathbb{R}^{\mathrm{Output}} \to \mathbb{R}$ (OpenAI's joint sliced principal density). Then $0 \le f(y) \le \prod_j K_j$ for every $y$, and $f$ is Lipschitz with constant $\bigl(\prod_j (K_j + 1)\bigr)\sum_j K_j\,(2K_j)$, products and sums over the active axes.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPathLiftDensity_cap_lipschitz` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedSlicedIdealDensity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B142` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedSlicedIdealDensity.lean#L251

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B142

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

theorem allocatedFixedPathLiftDensity_cap_lipschitz
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) :
    let K := allocatedFixedPathLiftRowCap P ha hδ
    (∀ y, allocatedFixedPathLiftDensity B P R σ hB lower width r y ∈
      Set.Icc (0 : ℝ) (∏ j, K j)) ∧
      LipschitzWith ((∏ j, (K j + 1)) * ∑ j, K j * (2 * K j))
        (allocatedFixedPathLiftDensity B P R σ hB lower width r) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
