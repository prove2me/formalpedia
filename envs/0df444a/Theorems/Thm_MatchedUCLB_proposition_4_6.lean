-- Prove2me | Theorems.Thm_MatchedUCLB_proposition_4_6
-- name    : MatchedUCLB.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:41.853761+00:00
-- url     : https://prove2.me/theorems/773102f0-2cc3-404b-805c-57b303e47585
-- title:
--   Proposition 4.6 — oracle indistinguishability, and one fixed instance keeping every candidate of group $j$ at gap $\ge 7\delta_j$
-- statement:
--   Let $q=p+\nu$ with $p\ge2$, $0<\nu\le1$. Fix the scalar parameters of Step 3 ($K$, $\eta$ as in Lemma 4.5, $\mu,\tau_0>0$), $m\ge32$, $L\ge1$ and $d\ge L(m+1)$, and put $n_m=\lfloor m/16\rfloor$. For every deterministic $p$th-order oracle algorithm there is an orthonormal phase frame $(v,u)$, with complete objective $F$, such that:
--
--   (a) *Oracle indistinguishability.* For every $0\le s\le n_mL$, let $j=\lfloor s/n_m\rfloor$ and let $\mathcal F_s$ be the objectives of all phase frames $(v',u')$ that agree with $(v,u)$ on the directions Step 4 has fixed after $s$ calls: the blocks $E_k$, $k<j$, the direction $v_j$ (if $j<L$) and the first $3(s-jn_m)$ chain directions of block $j$ (one more in group $0$, for $\hat x_0$). Every $F'\in\mathcal F_s$ returns the same oracle outputs as $F$ at the first $s$ evaluation points, i.e. the algorithm's transcript on $F'$ after $s$ calls equals its transcript on $F$.
--
--   (b) *One fixed objective and candidate gaps.* Along the algorithm's own run on $F$,
--
--   $$
--   F(\hat x_0)-\min F\ \ge\ 7\delta_0,\qquad F(\hat x_s)-\min F\ \ge\ 7\delta_j\quad\text{for } jn_m<s\le(j+1)n_m,\ 0\le j<L,
--   $$
--
--   where $\hat x_s$ is the candidate solution after $s$ oracle calls. Thus every algorithm needs more than $n_m$ calls per phase to leave the prefixes of that phase.
--
--   **Formalization Note** $\hat x_s$ is `A.candPt F s`, the candidate after $s$ calls when the algorithm is run on $F$. "$F(\hat x)-\min F\ge7\delta$" is written $F(y)+7\delta\le F(\hat x)$ for all $y$.
--
--   Differences from the source:
--   - encoding: ℝ^d, ∇^kF, ⟨∇F(x), v⟩ → EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ k F, fderiv ℝ F x v; reason: Lean convention; the norm of iteratedFDeriv is the operator norm of Sec. 3; same instances
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - encoding: the completion family F_s of the directions fixed in Step 4 after s calls, and ∇^kF'(x_ℓ) = a_{ℓ,k} for F' ∈ F_s, ℓ ≤ s, k ≤ p (4.19) → the objectives of all phase frames agreeing with the final frame on the blocks k < ⌊s/n_m⌋, on v_{⌊s/n_m⌋} and on the first 3(s mod n_m) (+1 in group 0) chain directions of the current block, with A.hist F' s = A.hist F s; reason: Step 4 fixes v_0 and at most one direction for x̂_0, at most three chain directions per call in order, and completes E_j and chooses v_{j+1} at the end of group j; fixing fewer directions only enlarges F_s, so the maximal count is equivalent to the existential over Step-4 choices; equal outputs at x_1..x_s ⇔ equal transcripts by determinism (Lemma F.1); F ∈ F_s gives F_s ≠ ∅
--   - encoding: the recorded transcript and 'every F ∈ F_{n_mL} reproduces the recorded evaluation points, oracle outputs, and candidate solutions' → the run of A on the final F (A.hist F, A.candPt F); reason: at s = n_mL every block is fixed, so F_{n_mL} = {F}, and by (a) the recorded transcript is the run on F
--   - encoding: F(x̂_s) − min F ≥ 7δ_j → ∀ y, F y + 7δ_j ≤ F (A.candPt F s); reason: equivalent; F attains its minimum (Lemma 4.5(b))
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Proposition 4.6, p.11, Eqs. (4.19)–(4.20)

import Mathlib
import Definitions.Def_MatchedUCLB_objective
import Definitions.Def_MatchedUCLB_objDelta
import Definitions.Def_MatchedUCLB_IsPhaseFrame
import Definitions.Def_MatchedUCLB_OracleAlg_candPt

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Proposition 4.6 (oracle indistinguishability and one fixed instance).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Proposition 4.6,
p.11: "Fix the scalar parameters specified in Step 3, `m ≥ 32`, `L ≥ 1`, and `d ≥ L(m + 1)`. Put
`n_m = ⌊m/16⌋`. For every deterministic pth-order oracle algorithm, the ordered orthonormal directions
in Step 4 can be chosen so that: (a) Oracle indistinguishability. For every `0 ≤ s ≤ n_mL`,
`F_s ≠ ∅`, `∇^kF(x_ℓ) = a_{ℓ,k}` (`F ∈ F_s`, `1 ≤ ℓ ≤ s`, `0 ≤ k ≤ p`) (4.19). (b) One fixed objective
and candidate gaps. Every `F ∈ F_{n_mL}` reproduces the recorded evaluation points, oracle outputs,
and candidate solutions when the algorithm runs on it through `n_mL` oracle calls, and satisfies, for
`jn_m < s ≤ (j + 1)n_m` and `0 ≤ j < L`, `F(x̂_s) − min F ≥ 7δ_j`, `F(x̂_0) − min F ≥ 7δ_0` (4.20)."
Step 4 and Step 5, pp.10–11: group `j` consists of calls `jn_m + 1, …, (j + 1)n_m`; the selection
starts with `v_0` and at most one direction for `x̂_0`, each call fixes at most three further chain
directions `u_{j,b+1}, …` of the current block in order, and after the last call of group `j` the
block `E_j` is completed and `v_{j+1}` chosen; `F_s` is the family of objectives (4.17) obtained by
completing the directions fixed after `s` calls.

**Formalization Note.** `q` is a separate real binder with the hypothesis `q = p + ν` (the matched order of the paper), so that every formula can be written in `q`. The scalar parameters of Step 3 are those of Lemma 4.5 (`K`, `η` fixed,
`μ, τ_0 > 0`); `F = objective q μ L τ₀ v u` for the final frame `(v, u)`, chosen after the algorithm.
The algorithm is `A : OracleAlg d p` (Definition B.1, (F.1)–(F.2)); `x̂_s = A.candPt F s` and the
recorded transcript `H_s` is `A.hist F s`. `F(x̂) − min F ≥ 7δ` is written `∀ y, F y + 7δ ≤ F x̂`.

(a) is stated with `F_s` the objectives of all phase frames `(v', u')` of the same `ℝ^d` that agree
with `(v, u)` on the directions fixed after `s` calls: with `j = ⌊s/n_m⌋`, all blocks `k < j`, the
starting direction `v_j` (when `j < L`) and the first `3(s − jn_m)` chain directions of block `j`, plus
one more in group `0` (the direction for `x̂_0`). This is the largest number Step 4 can fix; fixing
fewer only enlarges `F_s` and strengthens the claim, so the clause is the paper's (a). "`∇^kF'(x_ℓ) =
a_{ℓ,k}` for `ℓ ≤ s`, `k ≤ p`" is equivalent, by determinism of the run (Lemma F.1), to equality of
the transcripts `A.hist F' s = A.hist F s`; `F_s ≠ ∅` holds because `F ∈ F_s`. At `s = n_mL` every
block is fixed, so `F_{n_mL}` consists of `F` alone, and (b) is the gap statement for `F` along its
own run, which reproduces the transcript by definition. -/
theorem proposition_4_6 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) :
    ∀ (d m L : ℕ) (μ τ₀ : ℝ), 32 ≤ m → 1 ≤ L → L * (m + 1) ≤ d → 0 < μ → 0 < τ₀ →
    ∀ A : OracleAlg d p, ∃ (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)), IsPhaseFrame L v u ∧
      -- (a)
      (∀ s : ℕ, s ≤ L * (m / 16) →
        ∀ (v' : ℕ → EuclideanSpace ℝ (Fin d)) (u' : ℕ → Fin m → EuclideanSpace ℝ (Fin d)), IsPhaseFrame L v' u' →
          (∀ k : ℕ, k < s / (m / 16) → v' k = v k ∧ u' k = u k) →
          (s / (m / 16) < L → v' (s / (m / 16)) = v (s / (m / 16)) ∧
            ∀ i : Fin m, (i : ℕ) < 3 * (s % (m / 16)) + (if s < m / 16 then 1 else 0) →
              u' (s / (m / 16)) i = u (s / (m / 16)) i) →
          A.hist (objective q μ L τ₀ v' u') s = A.hist (objective q μ L τ₀ v u) s) ∧
      -- (b)
      (∀ y : EuclideanSpace ℝ (Fin d), objective q μ L τ₀ v u y + 7 * objDelta q μ m τ₀ 0 ≤ objective q μ L τ₀ v u (A.candPt (objective q μ L τ₀ v u) 0)) ∧
      ∀ j : ℕ, j < L → ∀ s : ℕ, j * (m / 16) < s → s ≤ (j + 1) * (m / 16) →
        ∀ y : EuclideanSpace ℝ (Fin d), objective q μ L τ₀ v u y + 7 * objDelta q μ m τ₀ j ≤ objective q μ L τ₀ v u (A.candPt (objective q μ L τ₀ v u) s) := by sorry

end MatchedUCLB
