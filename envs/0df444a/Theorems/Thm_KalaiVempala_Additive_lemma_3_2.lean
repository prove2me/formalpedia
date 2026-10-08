-- Prove2me | Theorems.Thm_KalaiVempala_Additive_lemma_3_2
-- name    : KalaiVempala.Additive.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:15.443987+00:00
-- url     : https://prove2.me/theorems/18bbd4e5-ee41-4cd2-bd89-6bd38c4a32e0
-- title:
--   Lemma 3.2, pp. 300–301 — [0,1/ε]ⁿ and v+[0,1/ε]ⁿ overlap in at least a (1 − ε|v|₁) fraction
-- statement:
--   **Overlap of translated cubes.** Let $\varepsilon > 0$, let $C = [0, 1/\varepsilon]^n$, and let $v \in \mathbb R^n$ with $|v|_1 = \sum_i |v_i|$. Then the cubes $C$ and $v + C$ overlap in at least a $(1 - \varepsilon |v|_1)$ fraction of the volume of $C$:
--
--   $$\frac{\operatorname{vol}\big(C \cap (v + C)\big)}{\operatorname{vol}(C)} \;\ge\; 1 - \varepsilon\,|v|_1 .$$
--
--   Equivalently, if $x$ is uniformly distributed on $C$, then $\Pr[x \in v + C] \ge 1 - \varepsilon |v|_1$. In the analysis of Follow the Perturbed Leader this says that the laws of $s_{1:t-1} + p_t$ and $s_{1:t} + p_t$, uniform on cubes shifted by $s_t$, agree on all but an $\varepsilon |s_t|_1$ fraction.
--
--   **Formalization Note** The fraction is the probability, under the uniform law `perturbLaw n ε` on $[0, 1/\varepsilon]^n$ from `OracleRO.ApproxFPL.FPL`, of the set $\{x : x - v \in C\} = v + C$. The left side is `ENNReal.ofReal (1 - ε|v|₁)`, which is $0$ when $\varepsilon |v|_1 \ge 1$, so the statement is then trivially true, as on the page. The hypothesis $\varepsilon > 0$ is added because the cube has side $1/\varepsilon$.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), pp. 300–301, Lemma 3.2

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Additive

theorem lemma_3_2 {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin n → ℝ) :
    ENNReal.ofReal (1 - ε * ∑ i, |v i|) ≤
      perturbLaw n ε {x | x - v ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹)} := by sorry

end KalaiVempala.Additive
