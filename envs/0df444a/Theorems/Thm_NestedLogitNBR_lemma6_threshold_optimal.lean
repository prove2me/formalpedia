-- Prove2me | Theorems.Thm_NestedLogitNBR_lemma6_threshold_optimal
-- name    : NestedLogitNBR.lemma6_threshold_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:43:27.351984+00:00
-- url     : https://prove2.me/theorems/7601fead-019c-433d-aff3-1f5ff53d882e
-- title:
--   Lemma 6 — the fractional nest problem (8) has a threshold optimal solution
-- statement:
--   Let nest $i$ have weights $v_{ij}\ge0$, revenues $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$ and dissimilarity parameter $\gamma_i\ge0$, with $n\ge1$, and let $x\in\mathbb R$. The problem
--
--   $$
--   \max_{z\in[0,1]^n}\ \Big(\sum_{j\in N}v_{ij}z_{j}\Big)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_{j}}{\sum_{j\in N}v_{ij}z_{j}}-x\right]\tag{8}
--   $$
--
--   has an optimal solution of the form $z^*_1=\dots=z^*_{k-1}=1$, $z^*_k\in[0,1]$, $z^*_{k+1}=\dots=z^*_n=0$ for some $k\in\{1,\dots,n\}$. In particular the maximum is attained.
--
--   So, up to one fractional product, a nested-by-revenue assortment solves the fractional relaxation of each nest's constraint; this is what makes the nested-by-revenue linear program almost feasible for (3).
--
--   Differences from the source:
--   - generalization: the standing assumptions on all nests → only the assumptions on nest i that the inequality uses; reason: the statement concerns nest i alone; every instance of the model satisfies them
--   - generalization: revenues of the model (read as r_ij ≥ 0 elsewhere in this mission) → no sign condition on r_ij; reason: the lemma does not need it; every instance with r_ij ≥ 0 is covered
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; reason: the inequality does not use it; every instance satisfying it is covered
--   - reading: the objective of (8) at z with Σ_j v_ij z_ij = 0 (0/0 in the paper) → 0 (power 0 and x/0 = 0, fracObj); reason: same convention as V_i(∅)^{γ_i}(R_i(∅) − x) = 0 (p. 41); a nest offering no weight contributes nothing (p. 7)
--   - encoding: there exists an optimal solution z*_i of (8) of the threshold form, for some k = 1,…,n → ∃ k : Fin n, ∃ ρ ∈ [0,1], the objective at threshold k ρ is ≥ the objective at every z ∈ [0,1]^n; hypothesis 0 < n; reason: same statement (the maximum exists and is attained at the threshold vector); n ≥ 1 makes N nonempty; k is 0-based
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), Lemma 6, p. 21

import Mathlib
import Definitions.Def_NestedLogitNBR_fracObj
import Definitions.Def_NestedLogitNBR_threshold

namespace NestedLogitNBR

/-- **Lemma 6: the fractional nest problem (8) has an optimal solution of threshold form.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), Lemma 6, p. 21: "There exists an optimal solution `z*_i` to the problem
`max_{z_i∈[0,1]^n} { (Σ_{j∈N} v_ij z_ij)^{γ_i} [ Σ_{j∈N} r_ij v_ij z_ij / Σ_{j∈N} v_ij z_ij − x ] }` (8)
such that `z*_i1 = 1, …, z*_i,k−1 = 1, z*_ik ∈ [0, 1], z*_i,k+1 = 0, …, z*_in = 0` for some
`k = 1, …, n`."

Hypotheses on nest `i` (pp. 7, 16): `v_ij ≥ 0`, `r_i1 ≥ … ≥ r_in`, `γ_i ≥ 0`; `n ≥ 1`.
The level `x` is any real number.

**Formalization Note.** "There exists an optimal solution of this form" is stated as: some
threshold vector `threshold k ρ` with `ρ ∈ [0, 1]` has an objective value at least that of every
`z ∈ [0,1]^n` (so the maximum exists and is attained there). Lean `k : Fin n` is the paper's
`k.val + 1`. The objective is `fracObj` (power replaced by `0` at total weight `0`). -/
theorem lemma6_threshold_optimal {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (i : Fin m) (hv : ∀ j, 0 ≤ v i j) (hord : Antitone (r i)) (hγ : 0 ≤ γ i) (hn : 0 < n)
    (x : ℝ) :
    ∃ k : Fin n, ∃ ρ ∈ Set.Icc (0 : ℝ) 1, ∀ z : Fin n → ℝ, (∀ j, z j ∈ Set.Icc (0 : ℝ) 1) →
      fracObj r v γ i z x ≤ fracObj r v γ i (threshold k ρ) x := by sorry

end NestedLogitNBR
