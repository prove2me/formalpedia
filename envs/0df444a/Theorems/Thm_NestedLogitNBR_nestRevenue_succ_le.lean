-- Prove2me | Theorems.Thm_NestedLogitNBR_nestRevenue_succ_le
-- name    : NestedLogitNBR.nestRevenue_succ_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:46:37.160681+00:00
-- url     : https://prove2.me/theorems/207b5581-be85-4c59-bc01-78e49514a2d3
-- title:
--   Average revenue of nested-by-revenue assortments decreases: $R_i(N_{i,j-1})\ge R_i(N_{ij})$
-- statement:
--   Let nest $i$ have weights $v_{ij}\ge0$ and revenues $r_{i1}\ge\dots\ge r_{in}$, and let $2\le j\le n$ with $V_i(N_{i,j-1})>0$. Then
--
--   $$
--   R_i(N_{i,j-1})\ \ge\ R_i(N_{ij}).
--   $$
--
--   $R_i(N_{ij})$ is the weighted average of the revenues of the first $j$ products, and the $j$-th product has the smallest of them. The proof of Theorem 7 states this as $\alpha^1_{ik}\ge1$ (p. 43, where the ratio is printed inverted); it is the first half of the proof of Lemma 14.
--
--   Differences from the source:
--   - generalization: the standing assumptions on all nests → only the assumptions on nest i that the inequality uses; reason: the statement concerns nest i alone; every instance of the model satisfies them
--   - generalization: revenues of the model (read as r_ij ≥ 0 elsewhere in this mission) → no sign condition on r_ij; reason: the averaging argument needs only the ordering; every instance with r_ij ≥ 0 is covered
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; reason: the inequality does not use it; every instance satisfying it is covered
--   - encoding: j = 2,…,n with R_i(N_i,j−1) a weighted average → k : Fin n with j = k.val + 1 and hypothesis 0 < V_i(N_i,j−1); reason: the positivity excludes only an all-zero-weight prefix, where the paper's average is undefined; it implies j ≥ 2
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), proof of Lemma 14, p. 43, unnumbered; also proof of Theorem 7, p. 43 (α¹_ik ≥ 1)

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_nestRevenue

namespace NestedLogitNBR

/-- **Adding the next product does not raise the average revenue: `R_i(N_i,j−1) ≥ R_i(N_ij)`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), proof of Lemma 14, p. 43, unnumbered: "Noting that
`R_i(N_ij) = Σ_{k=1}^{j} r_ik v_ik / Σ_{k=1}^{j} v_ik`, `R_ij(N_ij)` is the weighted average of
the revenues of the first `j` products in nest `i`. Since `r_i1 ≥ r_i2 ≥ … ≥ r_in`, it follows
that `R_i(N_i,j−1) ≥ R_i(N_ij)`." (The same fact is written `α¹_ik ≥ 1` on p. 43.)

Hypotheses on nest `i` (pp. 7, 16): `v_ij ≥ 0`, `r_i1 ≥ … ≥ r_in`.

**Formalization Note.** The paper's `j` is Lean `k.val + 1` for `k : Fin n`, so `N_ij` is
`nbr (k.val + 1)` and `N_i,j−1` is `nbr k.val`. The hypothesis `V_i(N_i,j−1) > 0` keeps
`R_i(N_i,j−1)` a genuine average (the paper's range is `j ≥ 2`, which it implies). -/
theorem nestRevenue_succ_le {m n : ℕ} (r v : Fin m → Fin n → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hord : Antitone (r i)) (k : Fin n)
    (hq : 0 < prefWeight v i (nbr k.val)) :
    nestRevenue r v i (nbr (k.val + 1)) ≤ nestRevenue r v i (nbr k.val) := by sorry

end NestedLogitNBR
