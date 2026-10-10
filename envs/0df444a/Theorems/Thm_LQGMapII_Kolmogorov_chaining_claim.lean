-- Prove2me | Theorems.Thm_LQGMapII_Kolmogorov_chaining_claim
-- name    : LQGMapII.Kolmogorov.chaining_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:03.18598+00:00
-- url     : https://prove2.me/theorems/466fc2c9-39f8-457d-9a1a-826bd93551d4
-- title:
--   Proof of Proposition 2.3, p. 31, last paragraph — dyadic increments ≤ t2^{−γk} give |f(u) − f(v)| ≤ c₃t|u − v|^γ on ∪_k𝒟_k
-- statement:
--   Fix $d \in \mathbb N$ and $\gamma > 0$. There is a constant $c_3 > 0$ with the following property. Let $f : [0,1]^d \to \mathbb R$ be any function and $t \in \mathbb R$, and suppose that
--   $$
--   2^{\gamma k} |f(u) - f(v)| \le t \quad \text{for every } k \in \mathbb N \text{ and every } \{u, v\} \in \widetilde{\mathcal D}_k,
--   $$
--   i.e. $\sup_{k}\max_{\{u,v\} \in \widetilde{\mathcal D}_k} 2^{\gamma k}|f(u) - f(v)| \le t$. Then
--   $$
--   |f(u) - f(v)| \le c_3\, t\, |u - v|^\gamma \quad \text{for all } u, v \in \textstyle\bigcup_k \mathcal D_k .
--   $$
--   Here $\mathcal D_k$ is the dyadic grid of mesh $2^{-k}$ in $[0,1]^d$, $\widetilde{\mathcal D}_k$ its set of adjacent pairs, and $|u - v|$ the Euclidean distance.
--
--   In the paper this is the closing claim of the proof of Proposition 2.3, applied to $f = X_\cdot(\omega)$ on the event of (2.12): it converts control of the dyadic increments into a Hölder bound on the dense set of dyadic points.
--
--   **Formalization Note** The claim is deterministic and is stated pathwise, for an arbitrary function $f$. The constant $c_3$ depends only on $d$ and $\gamma$ and is chosen before $f$ and $t$. It holds for every $\gamma > 0$; the restriction $\gamma < \beta/\alpha$ plays no role here and is not assumed.
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, proof of Proposition 2.3, p. 31, last paragraph

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMapII.Kolmogorov

/-- Proof of Proposition 2.3, p. 31, last paragraph: on the event
`sup_k max_{{u,v} ∈ 𝒟̃_k} 2^{γk} |X_u - X_v| ≤ t`, `|X_u - X_v| ≤ c₃ t |u - v|^γ` for all dyadic
`u, v`. Stated pathwise for an arbitrary function `f = X(·, ω)`; `c₃` depends on `d, γ` only. -/
theorem chaining_claim (d : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ (f : Cube d → ℝ) (t : ℝ),
        (∀ (k : ℕ) (u v : Cube d), IsAdjacentPair d k u v → (2 : ℝ) ^ (γ * k) * |f u - f v| ≤ t) →
        ∀ u v, u ∈ ⋃ k, dyadicGrid d k → v ∈ ⋃ k, dyadicGrid d k →
          |f u - f v| ≤ c₃ * t * dist u v ^ γ := by sorry

end LQGMapII.Kolmogorov
