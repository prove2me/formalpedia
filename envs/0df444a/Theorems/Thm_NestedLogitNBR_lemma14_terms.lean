-- Prove2me | Theorems.Thm_NestedLogitNBR_lemma14_terms
-- name    : NestedLogitNBR.lemma14_terms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:47:03.666243+00:00
-- url     : https://prove2.me/theorems/37106f14-47c4-4915-bd2b-9f6fb0f4a384
-- title:
--   Lemma 14 — for a nest with $\gamma_i>1$ both terms of the minimum in (6) are at least one
-- statement:
--   Let nest $i$ have weights $v_{ij}\ge0$, revenues $r_{ij}\ge0$ ordered $r_{i1}\ge\dots\ge r_{in}$, and $\gamma_i>1$. For $j=2,\dots,n$ with $V_i(N_{i,j-1})>0$ and $R_i(N_{ij})>0$ (the term of (6) is defined),
--
--   $$
--   \frac{R_i(N_{i,j-1})}{R_i(N_{ij})}\ \ge\ 1\qquad\text{and}\qquad \frac{R_i(N_{ij})}{R_i(N_{i,j-1})}\cdot\frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}}\ \ge\ 1 .
--   $$
--
--   Hence the term of (6) for nest $i$ and index $j$ is at least one, and so is the factor $\alpha$ of (6) (Lemma 14: if $\gamma_i>1$ for some $i$, then $\alpha\ge1$). This is what lets the proof of Theorem 7 replace $\alpha^1_{ik}\wedge(1\vee\alpha^2_{ik})$ by $\alpha$.
--
--   Differences from the source:
--   - reading: revenues r_ij with no stated sign → r_ij ≥ 0; reason: revenues are prices (BRIEF Reading 3, as in Theorem 7); the proof uses Σ_{k≤j} r_ik v_ik ≥ Σ_{k≤j−1} r_ik v_ik
--   - generalization: α ≥ 1 for α the expression (6), if γ_i > 1 for some i ∈ M → for the nest i with γ_i > 1 and each j = 2,…,n where the term is defined, both arguments of the minimum in (6) are ≥ 1; reason: this implies the lemma (any defined term of nest i is then ≥ 1, so the maximum (6) is ≥ 1) and is the conclusion of the paper's proof ('both terms of the minimum operator … for nest i are at least one'), which gives α ≥ 1 for the literal (6) as soon as one such term exists; 'factor6 ≥ 1' would hold by construction and carry no content
--   - encoding: the term of (6) is a quotient of R_i and V_i^{γ_i} values → hypotheses 0 < V_i(N_i,j−1) and 0 < R_i(N_ij); reason: exclude only the 0/0 cases where the paper's term is undefined; V_i(N_i,j−1) > 0 implies j ≥ 2
--   - generalization: the standing assumptions on all nests → only the assumptions on nest i that the inequality uses; reason: the statement concerns nest i alone; every instance of the model satisfies them
--   - encoding: index k = 1,…,n of the threshold product (and j = 2,…,n in (6)) → k : Fin n, with the paper's k = k.val + 1 (N_i,k−1 = nbr k.val, N_ik = nbr (k.val + 1)); reason: 0-based indexing; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), Lemma 14 and its proof, p. 43

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_nestRevenue

namespace NestedLogitNBR

/-- **Lemma 14: for a nest with `γ_i > 1`, both terms of the minimum in (6) are at least one.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), Lemma 14, p. 43: "Using `α` to denote the expression in (6), if we have `γ_i > 1` for some
`i ∈ M`, then `α ≥ 1`." Its proof concludes: "Therefore, both terms of the minimum operator in
the expression in (6) for nest `i` are at least one, which implies that `α` is also at least
one."

For nest `i` with `γ_i > 1` and an index `j = 2, …, n` of (6),
`R_i(N_i,j−1)/R_i(N_ij) ≥ 1` and `(R_i(N_ij)/R_i(N_i,j−1)) (V_i(N_ij)^{γ_i}/V_i(N_i,j−1)^{γ_i}) ≥ 1`.

Hypotheses on nest `i` (pp. 7, 16): `v_ij ≥ 0`, `r_ij ≥ 0`, `r_i1 ≥ … ≥ r_in`.

**Formalization Note.** The paper's `j` is Lean `k.val + 1` (`N_ij = nbr (k.val + 1)`,
`N_i,j−1 = nbr k.val`). The hypotheses `V_i(N_i,j−1) > 0` and `R_i(N_ij) > 0` say that the
term of (6) is defined (no `0/0`); `V_i(N_i,j−1) > 0` forces `j ≥ 2`. The statement is per
term, which gives `α ≥ 1` for the paper's (6) as soon as one such term exists; the bound
`factor6 ≥ 1` of the Lean factor holds by construction and is not the content of the lemma. -/
theorem lemma14_terms {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hr : ∀ j, 0 ≤ r i j) (hord : Antitone (r i)) (hγ : 1 < γ i)
    (k : Fin n) (hq : 0 < prefWeight v i (nbr k.val))
    (hR : 0 < nestRevenue r v i (nbr (k.val + 1))) :
    1 ≤ nestRevenue r v i (nbr k.val) / nestRevenue r v i (nbr (k.val + 1)) ∧
      1 ≤ nestRevenue r v i (nbr (k.val + 1)) / nestRevenue r v i (nbr k.val) *
        (prefWeight v i (nbr (k.val + 1)) ^ γ i / prefWeight v i (nbr k.val) ^ γ i) := by sorry

end NestedLogitNBR
