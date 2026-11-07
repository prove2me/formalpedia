-- Prove2me | Theorems.Thm_MetricMSO_theorem_3_5
-- name    : MetricMSO.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:05.91702+00:00
-- url     : https://prove2.me/theorems/6a1af85e-eb77-4269-8c5a-a815451191ef
-- title:
--   Theorem 3.5 — finite cyclic certificate for shortest paths
-- statement:
--   Let $M\ge3$ satisfy $M>\mathrm{cbl}(G)$ and let $P=v_0v_1\cdots v_r$ be a path with $s=v_0$ and $t=v_r$. Then $P$ is a shortest $s$-$t$ path if and only if there is an admissible labeling $c:V(G)\to\mathbb Z_M$ such that
--   $$c(v_{i+1})=c(v_i)+1\ \text{ in }\mathbb Z_M\quad\text{for every }0\le i<r.$$
--
--   Only $M$ labels are needed, so the certificate can be quantified by $M$ set variables.
--
--   Differences from the source:
--   - encoding: the path P = v₀…v_r → a walk p with Walk.IsPath, r = p.length and vᵢ = p.getVert i; reason: the same object
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Theorem 3.5, p.22 (PDF 24)

import Mathlib
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_Admissible

namespace MetricMSO

/-- **Theorem 3.5.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.22 (PDF 24): "Let M ≥ 3 satisfy
M > cbl(G), and let P = v0v1 · · · vr be a path with s = v0 and t = vr. Then P is a shortest s-t path
if and only if there exists an admissible labeling c: V(G) → ZM such that c(vi+1) = c(vi) + 1 in ZM
for every 0 ≤ i < r."

**Formalization Note** `P` is a walk with `Walk.IsPath`; `G.dist` is the true distance because `p`
joins `s` and `t`. -/
theorem theorem_3_5 {V : Type} [Fintype V] (G : SimpleGraph V) (M : ℕ) (hM : 3 ≤ M)
    (hcbl : cbl G < M) {s t : V} (p : G.Walk s t) (hp : p.IsPath) :
    p.length = G.dist s t ↔
      ∃ c : V → ZMod M, Admissible G c ∧
        ∀ i, i < p.length → c (p.getVert (i + 1)) = c (p.getVert i) + 1 := by sorry

end MetricMSO
