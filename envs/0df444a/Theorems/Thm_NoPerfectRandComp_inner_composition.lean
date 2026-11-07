-- Prove2me | Theorems.Thm_NoPerfectRandComp_inner_composition
-- name    : NoPerfectRandComp.inner_composition
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:46.77162+00:00
-- url     : https://prove2.me/theorems/b19959b2-0c57-43c8-8c02-7cac4cb6c5b2
-- title:
--   §2.4 — inner composition theorem of [8], $\mathrm{R}(f\circ g)=\Omega(\mathrm{R}(f)\,\mathrm{LR}(g))$
-- statement:
--   This is the inner composition theorem of Ben-David, Blais, Göös and Maystre, which the paper cites and uses.
--
--   There is an absolute constant $c > 0$ such that for all possibly partial Boolean functions $f$ and $g$ on finitely many variables,
--   $$
--   \mathrm{R}(f \circ g) \ \ge\ c\,\mathrm{R}(f)\,\mathrm{LR}(g) .
--   $$
--
--   It is the source of every lower bound on a composition in the mission: an inner function with small $\mathrm{LR}$ is the only possible counterexample to perfect composition from the inner side.
--
--   **Formalization Note** The constant is chosen before the coordinate types and the functions. The inequality is stated in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: R(f ∘ g) = Ω(R(f) LR(g)) → ∃ c > 0, uniform over all finite coordinate types and functions, c·R(f)·LR(g) ≤ R(f ∘ g) in [0,∞]; reason: definition of Ω; LR is valued in [0,∞]
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.4, p.6 (inner composition theorem, cited from [8] = Ben-David–Blais–Göös–Maystre, FOCS 2022, arXiv:2208.12896); also Eq. (1), p.2

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_LR
open scoped ENNReal

namespace NoPerfectRandComp

/-- The inner composition theorem of Ben-David–Blais–Göös–Maystre [8], as used in Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3),
§2.4, p.6 (cited from [8], not proved in the paper): `R(f ∘ g) = Ω(R(f) LR(g))` for all possibly
partial `f`, `g`.

**Formalization Note** The `Ω` is one absolute constant `c > 0`, chosen before the coordinate
types and the functions. The inequality is in `ℝ≥0∞` (`LR` may in principle be infinite). -/
theorem inner_composition :
    ∃ c : ℝ, 0 < c ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (f : PartialFn ι) (g : PartialFn κ),
      ENNReal.ofReal c * (R f : ℝ≥0∞) * LR g ≤ (R (f.comp g) : ℝ≥0∞) := by sorry

end NoPerfectRandComp
