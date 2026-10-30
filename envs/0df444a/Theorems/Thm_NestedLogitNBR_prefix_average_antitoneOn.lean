-- Prove2me | Theorems.Thm_NestedLogitNBR_prefix_average_antitoneOn
-- name    : NestedLogitNBR.prefix_average_antitoneOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:44:07.998617+00:00
-- url     : https://prove2.me/theorems/693ed86b-9050-42ca-ab2f-69868e744cd6
-- title:
--   The partial average revenue $(R_{i,k-1}+r_{ik}v_{ik}\rho)/(q_{i,k-1}+v_{ik}\rho)$ is decreasing in $\rho$
-- statement:
--   Let nest $i$ have weights $v_{ij}\ge0$ and revenues $r_{i1}\ge\dots\ge r_{in}$. For $k\ge2$ write $R_{i,k-1}=\sum_{j=1}^{k-1}r_{ij}v_{ij}$ and $q_{i,k-1}=\sum_{j=1}^{k-1}v_{ij}$, and assume $q_{i,k-1}>0$. Then
--
--   $$
--   \rho\ \longmapsto\ \frac{R_{i,k-1}+r_{ik}v_{ik}\rho}{q_{i,k-1}+v_{ik}\rho}
--   $$
--
--   is nonincreasing on $[0,1]$: adding a fraction $\rho$ of product $k$, whose revenue is at most that of the earlier products, does not raise the average revenue. In Case 1.a of the proof of Theorem 7 this bounds the factor in (19) by $R_i(N_{i,k-1})/R_i(N_{ik})$.
--
--   Differences from the source:
--   - generalization: the standing assumptions on all nests → only the assumptions on nest i that the inequality uses; reason: the statement concerns nest i alone; every instance of the model satisfies them
--   - generalization: revenues of the model (read as r_ij ≥ 0 elsewhere in this mission) → no sign condition on r_ij; reason: the monotonicity needs only the ordering; every instance with r_ij ≥ 0 is covered
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; reason: the inequality does not use it; every instance satisfying it is covered
--   - encoding: q_i,k−1 in a denominator (Case 1, k ≥ 2) → hypothesis 0 < q_i,k−1 = V_i(N_i,k−1); reason: excludes only the 0/0 case where the paper's quotient is undefined; it implies k ≥ 2, so the hypothesis k ≥ 2 is not stated separately
--   - encoding: decreasing in ρ (ρ ∈ [0,1]) → AntitoneOn on Set.Icc 0 1; reason: nonincreasing, as the paper's derivative sign ≤ 0 gives; the paper uses only the bound at ρ = 0
--   - encoding: index k = 1,…,n of the threshold product (and j = 2,…,n in (6)) → k : Fin n, with the paper's k = k.val + 1 (N_i,k−1 = nbr k.val, N_ik = nbr (k.val + 1)); reason: 0-based indexing; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7, Case 1.a), p. 41, unnumbered

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_revSum

namespace NestedLogitNBR

/-- **The partial average revenue is decreasing in the fractional level `ρ` (Case 1.a).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7, Case 1.a), p. 41, unnumbered: "It is simple to check that the
first derivative of `(R_i,k−1 + r_ik v_ik ρ)/(q_i,k−1 + v_ik ρ)` with respect to `ρ` has the same
sign as `r_ik q_i,k−1 − R_i,k−1` and we have `r_ik q_i,k−1 − R_i,k−1 = Σ_{j=1}^{k−1}(r_ik − r_ij) v_ij ≤ 0`,
where the last inequality is by the fact that `r_i1 ≥ r_i2 ≥ … ≥ r_in`. Thus, it follows that
`(R_i,k−1 + r_ik v_ik ρ)/(q_i,k−1 + v_ik ρ)` is decreasing in `ρ`".

Here `R_i,k−1 = revSum r v i (k−1)` (a sum) and `q_i,k−1 = V_i(N_i,k−1)`.

**Formalization Note.** Lean `k : Fin n` is the paper's `k.val + 1`, so `N_i,k−1` is
`nbr k.val`. "Decreasing" is `AntitoneOn` over `ρ ∈ [0, 1]`. The hypothesis
`q_i,k−1 > 0` keeps the quotient defined at `ρ = 0`; it also forces the paper's Case 1,
`k ≥ 2`. -/
theorem prefix_average_antitoneOn {m n : ℕ} (r v : Fin m → Fin n → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hord : Antitone (r i)) (k : Fin n)
    (hq : 0 < prefWeight v i (nbr k.val)) :
    AntitoneOn (fun ρ : ℝ => (revSum r v i k.val + r i k * v i k * ρ) /
      (prefWeight v i (nbr k.val) + v i k * ρ)) (Set.Icc 0 1) := by sorry

end NestedLogitNBR
