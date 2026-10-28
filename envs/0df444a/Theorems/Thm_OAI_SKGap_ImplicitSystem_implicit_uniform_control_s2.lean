-- Prove2me | Theorems.Thm_OAI_SKGap_ImplicitSystem_implicit_uniform_control_s2
-- name    : OAI.SKGap.ImplicitSystem.implicit_uniform_control_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:47:25.323982+00:00
-- url     : https://prove2.me/theorems/f51d4689-df1d-4c7e-8bac-3a4e0e6fb181
-- title:
--   OAI.SKGap.ImplicitSystem.implicit_uniform_control_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap.ImplicitSystem`):
--
--   ```lean
--   theorem implicit_uniform_control_s2 (j χ b r p : ℝ) (X J : E→L[ℝ]E)
--       (u m t ell q w y : E) (c : ℝ)
--       (s χ' p' c' b' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E)
--       {δ d B : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1) (hB : 0≤B)
--       (hX : ‖X‖≤B) (hX' : ∀i,‖X' i‖≤B) (hJ : ‖J‖≤B)
--       (hχ : |χ|≤B^2) (hχ' : ∀i,|χ' i|≤B^2)
--       (hu : ‖u‖≤B) (hm : ‖m‖≤d) (hm' : ∀i,‖m' i‖≤d) (ht : ‖t‖≤d)
--       (hell : ‖ell‖≤B*d) (hell' : ∀i,‖ell' i‖≤B*d) (hp : d*|p|≤B)
--       (hS : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
--       (hS' : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
--       (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
--         (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
--       (hSmall' : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
--         (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
--       (h : Equations j χ r p (X*X) J u m t ell w y c)
--       (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
--       (hDA : ∀V,columnNorm (fun i=>(s i • (X*X-X' i*X' i)) V)≤B*‖V‖)
--       (hDu : columnNorm (fun i=>s i • (u-u' i))≤B)
--       (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤B)
--       (hDm : columnNorm (fun i=>s i • (m-m' i))≤B*d)
--       (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤B*d)
--       (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤B) :
--       ‖w‖+d*|c|+‖y‖+columnNorm (fun i=>s i • (w-w' i))+
--         d*columnNorm (fun i=>s i*(c-c' i))+columnNorm (fun i=>s i • (y-y' i))≤
--           uniformControlBudget j δ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.ImplicitSystem.Equations`, `OAI.SKGap.ImplicitSystem.columnNorm`, `OAI.SKGap.ImplicitSystem.stableMatrix` and `OAI.SKGap.ImplicitSystem.uniformControlBudget` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

theorem implicit_uniform_control_s2 (j χ b r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell q w y : E) (c : ℝ)
    (s χ' p' c' b' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E)
    {δ d B : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1) (hB : 0≤B)
    (hX : ‖X‖≤B) (hX' : ∀i,‖X' i‖≤B) (hJ : ‖J‖≤B)
    (hχ : |χ|≤B^2) (hχ' : ∀i,|χ' i|≤B^2)
    (hu : ‖u‖≤B) (hm : ‖m‖≤d) (hm' : ∀i,‖m' i‖≤d) (ht : ‖t‖≤d)
    (hell : ‖ell‖≤B*d) (hell' : ∀i,‖ell' i‖≤B*d) (hp : d*|p|≤B)
    (hS : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hS' : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hSmall' : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    (hDA : ∀V,columnNorm (fun i=>(s i • (X*X-X' i*X' i)) V)≤B*‖V‖)
    (hDu : columnNorm (fun i=>s i • (u-u' i))≤B)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤B)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤B*d)
    (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤B*d)
    (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤B) :
    ‖w‖+d*|c|+‖y‖+columnNorm (fun i=>s i • (w-w' i))+
      d*columnNorm (fun i=>s i*(c-c' i))+columnNorm (fun i=>s i • (y-y' i))≤
        uniformControlBudget j δ B := by
  sorry
end SKGap.ImplicitSystem

end
end

end OAI
end
