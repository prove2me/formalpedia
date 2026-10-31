-- Prove2me | Theorems.Thm_MixedManna_lemma_9
-- name    : MixedManna.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:57.520395+00:00
-- url     : https://prove2.me/theorems/2f0a7a16-dfb4-425d-a754-45dd89d040b0
-- title:
--   Lemma 9 — LCP (13) solutions with p < P, r < R decode to competitive equilibria
-- statement:
--   Consider an instance satisfying the standing assumptions and $P>0$. For every $R$ with $R>P/|U_{ijk}|$ for all segments of nonzero slope that carry variables and every last-segment length $1+\varepsilon$, $\varepsilon>0$: every solution $(p,f,r,s)$ of LCP (13) (a solution of LCP (14) with $z=0$) with $p_j<P$ for all $j\in M$ and $r_i<R$ for all $i\in N$ gives a competitive equilibrium $(p^*,x^*)$, where
--
--   $$
--   p^*_j=P-p_j\ (j\in M^+),\qquad p^*_j=-(P-p_j)\ (j\in M^-),\qquad x^*_{ij}=\frac{\sum_kf_{ijk}}{P-p_j}.
--   $$
--
--   This is the half of Theorem 12 used by Theorem 14: the endpoint of Algorithm 1 is an equilibrium.
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - encoding: a solution to LCP (13) → a point of lcpSolutions with z = 0, for any δ; reason: LCP (13) is LCP (14) without z (p.20); at z = 0 the coefficients δ_j do not occur
--   - encoding: allocation x*_ij = Σ_k f_ijk / p*_j (p.45) → x*_ij = Σ_k f_ijk / (P − p_j) (decodeAlloc); reason: for a bad p*_j < 0 ≤ f_ijk and −f_ijk is the amount earned (p.17); the amount allocated is Σ_k f_ijk / |p*_j|
--   - generalization: R > P / U_min with U_min = min |U_ijk| over all (i, j, k) with U_ijk ≠ 0 (p.20; proof, p.45) → P < |U_σ| R for every segment σ of Seg with nonzero slope; reason: the proof uses the inequality only on segments that carry variables, and every R the paper allows satisfies it
--   - generalization: last segment of length 1 + ϵ for some small ϵ > 0 in the LCP (p.14, p.23) → every ε > 0 (lcpLength); reason: the proofs use only that the length exceeds 1; specializes to small ε
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Lemma 9, p.20 (PDF p.22), proof p.45

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsCompetitiveEquilibrium
import Definitions.Def_MixedManna_lcpSolutions
import Definitions.Def_MixedManna_decodePrice

namespace MixedManna

open Classical

/-- **Lemma 9** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.20): "In any solution to LCP (13) with `p_j < P`, `∀j ∈ M`, and
`r_i < R`, `∀i ∈ N`, all agents receive an optimal bundle and market clears w.r.t. prices `p*`
where `p*_j = (P − p_j)` for all goods `j ∈ M⁺` and `p*_j = −(P − p_j)` for all chores `j ∈ M⁻`."

Stated: for every `P > 0`, every `R` with `R > P / |U_ijk|` for all segments of nonzero slope that
carry variables, and every last-segment length `1 + ε`, `ε > 0`, every solution of LCP (13) (a
solution of LCP (14) with `z = 0`) with `p < P` and `r < R` decodes to a competitive equilibrium
`(p*, x*)`, `x*_ij = Σ_k f_ijk / (P − p_j)`.

**Formalization Note** LCP (13) is LCP (14) at `z = 0`, which does not depend on `δ`, so `δ` is
arbitrary. The condition on `R` is the paper's `R > P / U_min`, `U_min = min_{U_ijk ≠ 0} |U_ijk|`
(p.20; proof, p.45), required of the segments in `Seg I` only. -/
theorem lemma_9 {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P : ℝ) (hP : 0 < P) (R : ℝ)
    (hR : ∀ σ : Seg I, segSlope σ ≠ 0 → P < |segSlope σ| * R) (δ : M → ℝ) (ε : ℝ) (hε : 0 < ε)
    (x : LCPVar I) (hx : x ∈ lcpSolutions I P R δ ε) (hz : zv x = 0) (hp : ∀ j, pv x j < P)
    (hr : ∀ i, rv x i < R) :
    IsCompetitiveEquilibrium I (decodePrice I P (pv x)) (decodeAlloc I P x) := by sorry

end MixedManna
