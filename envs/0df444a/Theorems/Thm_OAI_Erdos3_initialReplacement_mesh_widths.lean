-- Prove2me | Theorems.Thm_OAI_Erdos3_initialReplacement_mesh_widths
-- name    : OAI.Erdos3.initialReplacement_mesh_widths
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:23:32.622737+00:00
-- url     : https://prove2.me/theorems/92c9bf2c-1972-4d4f-a95b-74634064718e
-- title:
--   Width bounds for the initial replacement source and parameter meshes
-- statement:
--   Let $I,J$ be types, let $\mathrm{sourceLo},\mathrm{sourceHi}\colon \mathrm{Option}\,J\times I\to\mathbb Z$ and $\mathrm{parLo},\mathrm{parHi}\colon J\to\mathbb Z$ with $\mathrm{sourceLo}(z)<\mathrm{sourceHi}(z)$ for every $z$ and $\mathrm{parLo}(j)<\mathrm{parHi}(j)$ for every $j$. Let $H\colon I\to\mathbb R$, real numbers $L\ge 0$, $K\ge 0$, $c>0$ and a natural number $D>0$. Assume that for every $z=(o,i)\in\mathrm{Option}\,J\times I$, `smoothPairCoefficientScale (H i) L o` $\le K\,(\mathrm{sourceHi}(z)-\mathrm{sourceLo}(z))$, where `smoothPairCoefficientScale H L` sends `none` to $H$ and every `some j` to $H/L$; and that $cL\le \mathrm{parHi}(j)-\mathrm{parLo}(j)$ for every $j$. Then: (1) for every $i\in I$, $(K+1)^{-1}H_i\le \mathrm{sourceHi}(\mathrm{none},i)-\mathrm{sourceLo}(\mathrm{none},i)$; (2) for every $z=(o,i)$, `smoothPairCoefficientScale (H i) L o` $\le K\cdot\mathrm{toNat}(\mathrm{sourceHi}(z)-\mathrm{sourceLo}(z))$; and (3) for every $j$, $L/D\le c^{-1}\,\mathrm{toNat}(\mathrm{parHi}(j)-\mathrm{parLo}(j))$, where $\mathrm{toNat}$ is the conversion $\mathbb Z\to\mathbb N$ (truncating negatives to $0$) followed by the cast to $\mathbb R$.
--
--   Lean: `OAI.Erdos3.initialReplacement_mesh_widths` in `lean/OAI/Combinatorics/Progressions/Estimates/InitialReplacementMeshWidths.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/InitialReplacementMeshWidths.lean#L25

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

theorem initialReplacement_mesh_widths {I J : Type*}
    (sourceLo sourceHi : Option J × I → ℤ) (parLo parHi : J → ℤ)
    (hsource : ∀ z, sourceLo z < sourceHi z) (hparameter : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L K c : ℝ} {D : ℕ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hc : 0 < c) (hD : 0 < D)
    (hsourceScale : ∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ))
    (hrelative : ∀ j, c * L ≤ ((parHi j - parLo j : ℤ) : ℝ)) :
    (∀ i, (K + 1)⁻¹ * H i ≤ ((sourceHi (none,i) - sourceLo (none,i) : ℤ) : ℝ)) ∧
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z).toNat : ℝ)) ∧
    (∀ j, L / (D : ℝ) ≤ c⁻¹ * ((parHi j - parLo j).toNat : ℝ)) := by
  sorry

end Erdos3
end
end OAI
