-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_lemma_9_2
-- name    : GoldieRenewal.Implicit.lemma_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:56.764002+00:00
-- url     : https://prove2.me/theorems/082a7045-66c7-48e3-baaf-28f922d02f4b
-- title:
--   Lemma 9.2 — if f ∈ L¹(ℝ), then the smoothing f̌ is dRi
-- statement:
--   Let $f\in L^1(\mathbb R)$ and $\check f(t) = \int_{-\infty}^t e^{-(t-u)}f(u)\,du$. Then $\check f$ is directly Riemann-integrable.
--
--   The smoothing removes the need for any regularity of $f$: in the proof of Theorem 2.3 the tail-difference function $g_1$ is only integrable, and $\check g_1$ is the function to which the key renewal theorem is applied.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 143, Lemma 9.2

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_DRi
open MeasureTheory

namespace GoldieRenewal.Implicit

/-- **Lemma 9.2** (Goldie 1991, Ann. Appl. Probab. 1(1), p. 143). If `f ∈ L¹(ℝ)`, then `f̌` is dRi,
where `f̌(t) := ∫_{−∞}^t e^{−(t−u)} f(u) du` (p. 128).

**Formalization Note** `f̌` is `smooth f`; dRi is `IsDRi` (Feller's definition). For `f ∈ L¹(ℝ)` the
integral defining `f̌(t)` converges absolutely for every `t`. -/
theorem lemma_9_2 (f : ℝ → ℝ) (hf : Integrable f) : IsDRi (smooth f) := by sorry

end GoldieRenewal.Implicit
