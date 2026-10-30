-- Prove2me | Theorems.Thm_NestedLogitNBR_ineq22
-- name    : NestedLogitNBR.ineq22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:46:11.421813+00:00
-- url     : https://prove2.me/theorems/cf3a1279-fe5e-4c95-ac63-240be7a03761
-- title:
--   Inequality (22) — the bound with $1\vee\alpha^2_{ik}$
-- statement:
--   Let nest $i$ have weights $v_{ij}\ge0$, revenues $r_{ij}\ge0$ ordered $r_{i1}\ge\dots\ge r_{in}$, and $\gamma_i\ge0$. For $k\ge2$ let $R_{i,k-1}=\sum_{j<k}r_{ij}v_{ij}$, $q_{i,k-1}=\sum_{j<k}v_{ij}>0$, $\rho\in[0,1]$, and $\alpha^2_{ik}=\frac{R_i(N_{ik})}{R_i(N_{i,k-1})}\frac{V_i(N_{ik})^{\gamma_i}}{V_i(N_{i,k-1})^{\gamma_i}}$. If $\hat x\ge0$, $\hat y_i\ge0$ and $\hat y_i\ge V_i(N_{i,k-1})^{\gamma_i}(R_i(N_{i,k-1})-\hat x)$ (the constraint of problem (4) for $N_{i,k-1}$), then
--
--   $$
--   (1\vee\alpha^2_{ik})\,\hat y_i\ \ge\ (q_{i,k-1}+v_{ik}\rho)^{\gamma_i}\left[\frac{R_{i,k-1}+r_{ik}v_{ik}\rho}{q_{i,k-1}+v_{ik}\rho}-(1\vee\alpha^2_{ik})\,\hat x\right].\tag{22}
--   $$
--
--   This is Case 1.b of the proof of Theorem 7; together with (20) it yields (24).
--
--   Differences from the source:
--   - reading: revenues r_ij with no stated sign → r_ij ≥ 0; reason: revenues are prices (BRIEF Reading 3, as in Theorem 7); the derivation goes through the endpoint bound, which needs r_ik ≥ 0
--   - generalization: (x̂, ŷ) an optimal solution of problem (4) with the nested-by-revenue candidates → any reals x̂ ≥ 0, ŷ_i ≥ 0 satisfying the single constraint of (4) for N_i,k−1; reason: the derivation uses only these facts, which every optimal solution satisfies (p. 41)
--   - generalization: the standing assumptions on all nests → only the assumptions on nest i that the inequality uses; reason: the statement concerns nest i alone; every instance of the model satisfies them
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; reason: the inequality does not use it; every instance satisfying it is covered
--   - encoding: q_i,k−1 in a denominator (Case 1, k ≥ 2) → hypothesis 0 < q_i,k−1 = V_i(N_i,k−1); reason: excludes only the 0/0 case where the paper's quotient is undefined; it implies k ≥ 2, so the hypothesis k ≥ 2 is not stated separately
--   - reading: α²_ik when R_i(N_i,k−1) = 0 (undefined in the paper) → 0 (x/0 = 0), so 1 ∨ α²_ik = 1; reason: then r_ik = 0 as well and the right side is ≤ 0, so the inequality still holds; no hypothesis R_i(N_i,k−1) > 0 is added
--   - encoding: index k = 1,…,n of the threshold product (and j = 2,…,n in (6)) → k : Fin n, with the paper's k = k.val + 1 (N_i,k−1 = nbr k.val, N_ik = nbr (k.val + 1)); reason: 0-based indexing; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7, Case 1.b), p. 42, eq. (22)

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_revSum
import Definitions.Def_NestedLogitNBR_nestRevenue
import Definitions.Def_NestedLogitNBR_nestAttraction

namespace NestedLogitNBR

/-- **Inequality (22) (Case 1.b of the proof of Theorem 7).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), App. A.1, p. 42, eq. (22):
`(1 ∨ α²_ik) ŷ_i ≥ (q_i,k−1 + v_ik ρ)^{γ_i} [ (R_i,k−1 + r_ik v_ik ρ)/(q_i,k−1 + v_ik ρ) − (1 ∨ α²_ik) x̂ ]`,
with "`α²_ik = (R_i(N_ik)/R_i(N_i,k−1)) (V_i(N_ik)^{γ_i}/V_i(N_i,k−1)^{γ_i})`" (p. 42) and
`a ∨ b = max{a, b}`, derived from the constraint of problem (4) for nest `i` and `N_i,k−1`,
and `x̂ ≥ 0`, `ŷ_i ≥ 0`.

Hypotheses on nest `i` (pp. 7, 16): `v_ij ≥ 0`, `r_ij ≥ 0`, `r_i1 ≥ … ≥ r_in`, `γ_i ≥ 0`;
`ρ ∈ [0, 1]`.

**Formalization Note.** Lean `k : Fin n` is the paper's `k.val + 1` (`N_i,k−1 = nbr k.val`,
`N_ik = nbr (k.val + 1)`); `R_i,k−1 = revSum r v i k.val` is a sum. Powers are `Real.rpow`.
The hypothesis `q_i,k−1 > 0` keeps the quotient defined; it forces `k ≥ 2` (Case 1). -/
theorem ineq22 {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hr : ∀ j, 0 ≤ r i j) (hord : Antitone (r i)) (hγ : 0 ≤ γ i)
    (x yi : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ yi) (k : Fin n)
    (hk : nestAttraction v γ i (nbr k.val) * (nestRevenue r v i (nbr k.val) - x) ≤ yi)
    (hq : 0 < prefWeight v i (nbr k.val)) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (prefWeight v i (nbr k.val) + v i k * ρ) ^ γ i *
        ((revSum r v i k.val + r i k * v i k * ρ) / (prefWeight v i (nbr k.val) + v i k * ρ) -
          max 1 (nestRevenue r v i (nbr (k.val + 1)) / nestRevenue r v i (nbr k.val) *
            (prefWeight v i (nbr (k.val + 1)) ^ γ i / prefWeight v i (nbr k.val) ^ γ i)) * x) ≤
      max 1 (nestRevenue r v i (nbr (k.val + 1)) / nestRevenue r v i (nbr k.val) *
          (prefWeight v i (nbr (k.val + 1)) ^ γ i / prefWeight v i (nbr k.val) ^ γ i)) * yi := by sorry

end NestedLogitNBR
