-- Prove2me | Theorems.Thm_OAI_Erdos3_slicedDetection_kernel_cutoff_bound_s2
-- name    : OAI.Erdos3.slicedDetection_kernel_cutoff_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:36.190756+00:00
-- url     : https://prove2.me/theorems/31f1ef26-f8ba-4fa5-bc1c-31ddc7963f81
-- title:
--   The scalar kernel cutoff at the sliced-detection gain is at most the exponential of the logarithmic kernel budget
-- statement:
--   Let $s, C, \mathrm{count}$ be natural numbers, let $G$ be a finite type, and let $p, q, a, \alpha$ be real numbers with $0 \le p$, $0 \le q$, $0 \le a$ and $e^{-a} \le \alpha$. Put
--   $$\mathrm{gain} = e^{-((5p+20)\,\mathrm{count} + p + 2)} \cdot \frac{\alpha}{2} \cdot \bigl(e^{-(q+C)^{C}}\bigr)^{2^{s+1}},$$
--   let $\mathrm{gainLog} = $ `slicedDetectionGainLog s C count p q a` $= (5p+20)\,\mathrm{count} + p + 2 + a + 1 + 2^{s+1}(q+C)^{C}$ (defined by OpenAI), and let $R = \mathrm{gainLog} + p + 4$. Then
--   $$\texttt{scalarKernelCutoff}\ (\mathrm{Fin}\,(s+1))\ G\ 1\ \bigl\lceil e^{p+1} \bigr\rceil\ (\mathrm{gain}/2) \;\le\; \exp\bigl(\texttt{scalarKernelLogarithmicBudget}\ (\mathrm{Fin}\,(s+1))\ G\ R\bigr),$$
--   where $\lceil \cdot \rceil$ is the natural-number ceiling, the left side (a natural number) is read as a real number, and `scalarKernelCutoff I J M D η` (a natural number) and `scalarKernelLogarithmicBudget I J R` (a real number) are explicit kernel-cutoff quantities defined by OpenAI for finite types $I, J$; here $I = \mathrm{Fin}\,(s+1)$ is the type $\{0, \dots, s\}$ and $J = G$.
--
--   Lean: `OAI.Erdos3.slicedDetection_kernel_cutoff_bound_s2`, which states OpenAI's `OAI.Erdos3.slicedDetection_kernel_cutoff_bound` (in `lean/OAI/Combinatorics/Progressions/Dynamics/CanonicalDetectedScaleInputBudget.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B065` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/CanonicalDetectedScaleInputBudget.lean (declaration OAI.Erdos3.slicedDetection_kernel_cutoff_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B065

section

namespace OAI

section

namespace Erdos3

theorem slicedDetection_kernel_cutoff_bound_s2 (s C count : ℕ) (G : Type*) [Fintype G]
    {p q a α : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hα : Real.exp (-a) ≤ α) :
    let gain := (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
      Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1))
    let gainLog := slicedDetectionGainLog s C count p q a
    let R := gainLog + p + 4
    (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2) : ℝ) ≤
      Real.exp (scalarKernelLogarithmicBudget (Fin (s + 1)) G R) := by
  sorry

end Erdos3

end

end OAI
end
