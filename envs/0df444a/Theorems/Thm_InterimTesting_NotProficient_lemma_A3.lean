-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A3
-- name    : InterimTesting.NotProficient.lemma_A3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:48.813354+00:00
-- url     : https://prove2.me/theorems/b620a290-3574-45ec-bb66-85c13bd6a239
-- title:
--   Lemma A3, p. A7 (PDF 33) — under (14), 𝒯1(N,1,S0) ≥ 𝒯1(P,0,S0)
-- statement:
--   Suppose condition (14) (= (A26)) holds:
--   $$\frac{(1-\phi_{P|P})\phi_{P|N}}{\phi_{P|P}-\phi_{P|N}}\le\frac{(1-(A+B))B}{A}.$$
--   Then, under the formative assessment and for either starting state $S_0$,
--   $$\mathcal T_1(N,1,S_0)\ge\mathcal T_1(P,0,S_0):$$
--   the second-period threshold after a proficient result with no first-period effort is never above the threshold after a not-proficient result with full first-period effort.
--
--   This ordering of the four second-period thresholds is what makes the first-period problem tractable under (14).
--
--   **Formalization Note** (14) is stated cross-multiplied (`Cond14`), which also covers $\phi_{P|P}=\phi_{P|N}$.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A7 (PDF 33), Lemma A3, (A26)–(A27)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A3, p. A7: under (A26) = (14), `𝒯1(N, 1, S0) ≥ 𝒯1(P, 0, S0)` (formative assessment). -/
theorem lemma_A3 (θ : Params) (hθ : θ.Standing) (h14 : Cond14 θ) (S0 : Prof) :
    T1 θ false S0 0 .P ≤ T1 θ false S0 1 .N := by sorry

end InterimTesting.NotProficient
