-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_reduction_encode_polyTime
-- name    : NSWApxHard.Reduction.reduction_encode_polyTime
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T21:38:45.975658+00:00
-- url     : https://prove2.me/theorems/0097d088-ef18-460e-8c07-d288a9ad0aa0
-- title:
--   Polynomial-time encoding of the Nash social welfare reduction instance
-- statement:
--   Let $m_0 \ge 1$ and $0 \le a < b$ be fixed natural numbers with $b > 0$, and define the rational parameter
--
--   $$
--   \alpha' = \frac{m_0 + 2}{3m_0 + 3} \in \left(\frac{1}{3}, \frac{1}{2}\right)
--   $$
--
--   so that $1 + \alpha' = \frac{4m_0 + 5}{3m_0 + 3}$. Given a 3-regular graph input $I = (N, G)$ on $N > 0$ vertices, set $k = \lfloor a N / b \rfloor < N$. In Lee's reduction (Section 2, p. 2), the reduced Nash social welfare instance has $n = |\mathrm{Agent}(G)| = \frac{5}{2} N$ agents (the $N$ vertices and $\frac{3}{2} N$ edges of $G$) and $m = |\mathrm{Item}(G, k)| = k + \frac{9}{2} N$ items ($k$ vertex items and $3|E| = \frac{9}{2} N$ edge-endpoint items), with rational utilities $\mathrm{redUtil}(G, k, \alpha')$ taking values in $\{0, 1, \frac{2m_0 + 1}{3m_0 + 3}, \frac{m_0 + 1}{3m_0 + 3}, \frac{m_0 + 2}{3m_0 + 3}\}$.
--
--   Scaling all utilities by the common integer factor $S = (3m_0 + 3)(4m_0 + 5)$ yields integer utilities
--
--   $$
--   u(\text{ag}, \text{it}) = (3m_0 + 3)(4m_0 + 5) \cdot \mathrm{redUtil}(G, k, \alpha')(\text{ag}, \text{it}) \in \mathbb{N},
--   $$
--
--   and scaling the target welfare threshold $(1 + \alpha')^{(3k - 1.5N)/n}$ by $S$ raises its $n$-th power (where $n = 2.5 N$) to the exact positive integer product threshold
--
--   $$
--   T = S^n (1 + \alpha')^{3k - 1.5N} = (3m_0 + 3)^{4N - 3k} (4m_0 + 5)^{N + 3k}.
--   $$
--
--   There exist a reduction map $P : \mathrm{GraphInput} \to \mathrm{NSWInput}$ and a polynomial-time computable bit-list transducer $g : \mathrm{List\ Bool} \to \mathrm{List\ Bool}$ such that for every valid 3-regular graph input $I = (N, G)$ with $N > 0$, $\mathrm{encNSW}(P(I)) = g(\mathrm{encGraph}(I))$, $(P(I)).T = T$, and the agents and items of $P(I)$ are in bijection with $\mathrm{Agent}(G)$ and $\mathrm{Item}(G, k)$ with the scaled integer utilities above.
-- source:
--   Euiwoong Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, Information Processing Letters 122 (2017), 17–20, https://arxiv.org/pdf/1507.01159, Section 2, p. 2

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_NSWApxHard_Reduction_Welfare
import Definitions.Def_NSWApxHard_Reduction_CubicVC
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lee, §2, p. 2: for fixed integer parameters `m₀ ≥ 1` and `a < b` with `b > 0`, the reduction
from a 3-regular graph input `I = (N, G)` with `k = ⌊a N / b⌋` to an integer-utility Nash social
welfare instance `P I` (obtained by scaling the rational utilities `redUtil I.G k α'` with
`α' = (m₀ + 2) / (3m₀ + 3)` by the common denominator `(3m₀ + 3)(4m₀ + 5)` and setting the
product threshold `T = (3m₀ + 3)^{4N - 3k} (4m₀ + 5)^{N + 3k}`) is computable in polynomial time
with respect to the canonical encodings `encGraph` and `encNSW`. -/
theorem reduction_encode_polyTime (m₀ a b : ℕ) (hm₀ : 1 ≤ m₀) (hb : 0 < b) (hab : a < b) :
    ∃ (P : GraphInput → NSWInput) (g : List Bool → List Bool),
      CookPvsNP.PolyTimeComputable g ∧
      ∀ (I : GraphInput) [DecidableRel I.G.Adj], 0 < I.N → IsCubic I.G →
        let k := (a * I.N) / b
        encNSW (P I) = g (encGraph I) ∧
        (P I).T = (3 * m₀ + 3) ^ (4 * I.N - 3 * k) * (4 * m₀ + 5) ^ (I.N + 3 * k) ∧
        ∃ (eA : Fin (P I).n ≃ Agent I.G) (eB : Fin (P I).m ≃ Item I.G k),
          ∀ (ag : Fin (P I).n) (it : Fin (P I).m),
            ((P I).u ag it : ℝ) =
              ((3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5)) *
                redUtil I.G k (((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) (eA ag) (eB it) := by sorry

end NSWApxHard.Reduction
