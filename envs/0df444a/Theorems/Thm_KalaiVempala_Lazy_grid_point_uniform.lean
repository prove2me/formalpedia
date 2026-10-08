-- Prove2me | Theorems.Thm_KalaiVempala_Lazy_grid_point_uniform
-- name    : KalaiVempala.Lazy.grid_point_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:46:20.916694+00:00
-- url     : https://prove2.me/theorems/79a6eb6d-6c74-416d-b616-f61bbd71ad64
-- title:
--   Proof of Lemma 1.2 (FLL case), pp. 302–303 — the grid point g_{t−1} is uniform over s_{1:t−1} + [0,1/ε]ⁿ, like FPL
-- statement:
--   **The FLL grid point is distributed like FPL's perturbed point.** Let $\varepsilon > 0$, let $p$ be uniform on $[0, 1/\varepsilon]^n$, and for $x \in \mathbb R^n$ let $g(x, p)$ be the unique point of the grid $p + \tfrac1\varepsilon \mathbb Z^n$ in $x + [0, 1/\varepsilon)^n$. Then $g(x, p)$ has the same law as $x + p$:
--
--   $$\operatorname{Law}_{p \sim U}\big(g(x, p)\big) \;=\; \operatorname{Law}_{p \sim U}\big(x + p\big),$$
--
--   the uniform distribution on $x + [0, 1/\varepsilon]^n$. With $x = s_{1:t-1}$ this says that the point at which FLL($\varepsilon$) evaluates the oracle on period $t$ is distributed exactly as the point $s_{1:t-1} + p_t$ of FPL($\varepsilon$), so the two algorithms have the same expected cost on every period.
--
--   **Formalization Note** Both sides are push-forwards (`Measure.map`) of `perturbLaw n ε`; the grid point is the explicit formula `fllGridPoint`, which is measurable. The paper's half-open cube $x + [0,1/\varepsilon)^n$ and the closed cube differ by a Lebesgue-null set, so the closed-cube law `perturbLaw` is used on both sides. The page's "inside $s_{t-1} + [0, 1/\varepsilon)^n$" is read as $s_{1:t-1} + [0, 1/\varepsilon)^n$, as in the description of FLL on the same page.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), pp. 302–303, proof of Lemma 1.2 (FLL case), and the sentence after the definition of FLL(ε), p. 302

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Lazy

theorem grid_point_uniform {n : ℕ} (ε : ℝ) (hε : 0 < ε) (x : Fin n → ℝ) :
    (perturbLaw n ε).map (fllGridPoint ε x) = (perturbLaw n ε).map (fun p => x + p) := by sorry

end KalaiVempala.Lazy
