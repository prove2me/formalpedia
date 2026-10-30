-- Prove2me | Theorems.Thm_NestedLogitNBR_endpoint_bound
-- name    : NestedLogitNBR.endpoint_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:45:24.788589+00:00
-- url     : https://prove2.me/theorems/a49536de-b39c-4729-a1f5-aaab792d1944
-- title:
--   The endpoint bound of Case 1.b: the factor in (21) is at most $1\vee\alpha^2_{ik}$
-- statement:
--   Let nest $i$ have weights $v_{ij}\ge0$, revenues $r_{ij}\ge0$ ordered $r_{i1}\ge\dots\ge r_{in}$, and $\gamma_i\ge0$. For $k\ge2$ let $R_{i,k-1}=\sum_{j<k}r_{ij}v_{ij}$, $q_{i,k-1}=\sum_{j<k}v_{ij}>0$ and
--
--   $$
--   \alpha^2_{ik}=\frac{R_i(N_{ik})}{R_i(N_{i,k-1})}\cdot\frac{V_i(N_{ik})^{\gamma_i}}{V_i(N_{i,k-1})^{\gamma_i}}.
--   $$
--
--   Then for every $\rho\in[0,1]$
--
--   $$
--   \frac{R_{i,k-1}+r_{ik}v_{ik}\rho}{(q_{i,k-1}+v_{ik}\rho)^{1-\gamma_i}}\cdot\frac{q_{i,k-1}^{1-\gamma_i}}{R_{i,k-1}}\ \le\ 1\vee\alpha^2_{ik},\qquad a\vee b=\max\{a,b\}.
--   $$
--
--   The two values on the right are the left side at $\rho=0$ and $\rho=1$; the paper argues that the left side, as a function of $\rho$, is maximized at an endpoint. This bound turns (21) into (22).
--
--   Differences from the source:
--   - reading: revenues r_ij with no stated sign → r_ij ≥ 0; reason: revenues are prices (BRIEF Reading 3, as in Theorem 7); the endpoint maximum needs r_ik ≥ 0 (the derivative of the expression in ρ then changes sign at most once, from − to +)
--   - generalization: the standing assumptions on all nests → only the assumptions on nest i that the inequality uses; reason: the statement concerns nest i alone; every instance of the model satisfies them
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; reason: the inequality does not use it; every instance satisfying it is covered
--   - encoding: q_i,k−1 in a denominator (Case 1, k ≥ 2) → hypothesis 0 < q_i,k−1 = V_i(N_i,k−1); reason: excludes only the 0/0 case where the paper's quotient is undefined; it implies k ≥ 2, so the hypothesis k ≥ 2 is not stated separately
--   - reading: the factor (R_i,k−1 + r_ik v_ik ρ)/(q_i,k−1 + v_ik ρ)^{1−γ_i} · q_i,k−1^{1−γ_i}/R_i,k−1 when R_i,k−1 = 0 (undefined in the paper) → 0 (x/0 = 0); reason: the bound is then trivial; no hypothesis R_i,k−1 > 0 is added
--   - encoding: the expression is maximized at ρ = 0 or ρ = 1, and the resulting bound → the bound itself, for every ρ ∈ [0,1]; reason: this is what the proof uses; the remark on the second derivative is a proof step, not part of the claim
--   - encoding: index k = 1,…,n of the threshold product (and j = 2,…,n in (6)) → k : Fin n, with the paper's k = k.val + 1 (N_i,k−1 = nbr k.val, N_ik = nbr (k.val + 1)); reason: 0-based indexing; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7, Case 1.b), p. 42, unnumbered

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_revSum
import Definitions.Def_NestedLogitNBR_nestRevenue

namespace NestedLogitNBR

/-- **The endpoint bound of Case 1.b of the proof of Theorem 7.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), App. A.1, p. 42, unnumbered: "this expression is maximized at either `ρ = 0` or `ρ = 1`.
In this case, we can bound the expression that multiplies `ŷ_i` and `x̂` in (21) as
`(R_i,k−1 + r_ik v_ik ρ)/(q_i,k−1 + v_ik ρ)^{1−γ_i} · q_i,k−1^{1−γ_i}/R_i,k−1 ≤ 1 ∨ R_ik/q_ik^{1−γ_i} · q_i,k−1^{1−γ_i}/R_i,k−1
= 1 ∨ (R_i(N_ik)/R_i(N_i,k−1)) (V_i(N_ik)^{γ_i}/V_i(N_i,k−1)^{γ_i})`, where we use
`a ∨ b = max{a, b}`." The right-hand term is `α²_ik` (p. 42).

Hypotheses on nest `i` (pp. 7, 16): `v_ij ≥ 0`, `r_ij ≥ 0`, `r_i1 ≥ … ≥ r_in`, `γ_i ≥ 0`;
`ρ ∈ [0, 1]`.

**Formalization Note.** Lean `k : Fin n` is the paper's `k.val + 1` (`N_i,k−1 = nbr k.val`,
`N_ik = nbr (k.val + 1)`); `R_i,k−1 = revSum r v i k.val` is a sum. Powers are `Real.rpow` of
positive bases. The hypothesis `q_i,k−1 > 0` keeps the expression defined; it forces `k ≥ 2`.
When `R_i,k−1 = 0` the left side is `0` in Lean (`x / 0 = 0`). The statement is the bound
itself, for every `ρ ∈ [0, 1]`, not the paper's remark on the second derivative. -/
theorem endpoint_bound {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hr : ∀ j, 0 ≤ r i j) (hord : Antitone (r i)) (hγ : 0 ≤ γ i)
    (k : Fin n) (hq : 0 < prefWeight v i (nbr k.val)) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (revSum r v i k.val + r i k * v i k * ρ) / (prefWeight v i (nbr k.val) + v i k * ρ) ^ (1 - γ i) *
        (prefWeight v i (nbr k.val) ^ (1 - γ i) / revSum r v i k.val) ≤
      max 1 (nestRevenue r v i (nbr (k.val + 1)) / nestRevenue r v i (nbr k.val) *
        (prefWeight v i (nbr (k.val + 1)) ^ γ i / prefWeight v i (nbr k.val) ^ γ i)) := by sorry

end NestedLogitNBR
