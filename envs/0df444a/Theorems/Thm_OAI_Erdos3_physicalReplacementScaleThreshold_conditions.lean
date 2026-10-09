-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalReplacementScaleThreshold_conditions
-- name    : OAI.Erdos3.physicalReplacementScaleThreshold_conditions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:49:22.721546+00:00
-- url     : https://prove2.me/theorems/59709d46-5537-4e2a-9614-8bd7415ff444
-- title:
--   A scale above the physical replacement threshold meets every replacement condition
-- statement:
--   Let $J$ be a finite type with decidable equality, $n \in \mathbb{N}$, $k \in J$, $Q \in \mathbb{N}$, $C, \kappa \in \mathbb{R}$, $\mathrm{degree} \in \mathbb{N}$, $\mathrm{modLog}, \mathrm{dimLog} \in \mathbb{R}$, and let $A, \varepsilon, L, H$ be real numbers and $N, e$ natural numbers, with $0 \le C$, $0 \le A$, $0 < \varepsilon$, $1 \le L$ and $2 \le e$. Suppose
--   $$\texttt{physicalReplacementScaleThreshold}\ n\ k\ Q\ C\ \kappa\ A\ \varepsilon\ \mathrm{degree}\ \mathrm{modLog}\ \mathrm{dimLog} \cdot L^{e} \le H \quad\text{and}\quad H \le 2N,$$
--   where `physicalReplacementScaleThreshold` is an explicit real-valued threshold of OpenAI. Put $\delta = $ `physicalPairPointAccuracy n k Q C κ A ε`, $\rho = $ `physicalPairGridAccuracy n k C κ A ε` and $a = $ `physicalMeanAccuracyLog n k Q C κ A degree ε` (OpenAI's explicit real-valued accuracies; $a$ is $-\log$ of `physicalPairMeanAccuracy n k Q C κ A degree ε`). Then $0 < H$, $2 C L^2 / H \le \delta$, $4 \le \rho H$, $\exp(\mathrm{modLog} \cdot 2\,\mathrm{degree} + a + \mathrm{dimLog} + 1) \le \rho H / 4$, $Q \le N$, $8 \lambda \le H / L$, and $\rho H \le 2N$, where $\lambda = $ `probabilityProfileLipschitz`, the $\mathbb{R}_{\ge 0}$-valued constant OpenAI chooses as a Lipschitz constant of a smooth probability profile.
--
--   Lean: `OAI.Erdos3.physicalReplacementScaleThreshold_conditions` in `lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean#L210

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem physicalReplacementScaleThreshold_conditions {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) (modLog dimLog : ℝ)
    {A epsilon L H : ℝ} {N e : ℕ} (hC : 0 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hL : 1 ≤ L) (he : 2 ≤ e)
    (hscale : physicalReplacementScaleThreshold n k Q C κ A epsilon degree modLog dimLog * L ^ e ≤ H)
    (hupper : H ≤ 2 * (N : ℝ)) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    let accLog := physicalMeanAccuracyLog n k Q C κ A degree epsilon
    0 < H ∧ 2 * C * L ^ 2 / H ≤ delta ∧ 4 ≤ rho * H ∧
      Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ rho * H / 4 ∧
      (Q : ℝ) ≤ N ∧ 8 * (probabilityProfileLipschitz : ℝ) ≤ H / L ∧ rho * H ≤ 2 * N := by
  sorry

end Erdos3
end
end OAI
