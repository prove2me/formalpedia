-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_deterministic_local_centers
-- name    : HardCoreLocalSampling.Local.deterministic_local_centers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:11.938436+00:00
-- url     : https://prove2.me/theorems/f0cee04f-2e87-4791-bd12-f3bcef214fb2
-- title:
--   Lemma 9 — Deterministic local centers
-- statement:
--   For every fixed rational $\tau>0$, each internal subproblem $s$ admits a deterministic dyadic center $c_s\in[0,U]$ with $|c_s-y_s|\le\tau$. All centers lie on one finite dyadic grid in $[0,\bar U]$, $\bar U=2+\lambda$. Computing a center explores a constant-size neighborhood in its deletion computation tree, with constants depending only on $\Delta,\lambda,\tau$.
--
--   Precisely, there are a height $h$, a grid exponent $k$ and a rule $\Phi$ with $c_s=\Phi(\text{view}_h(s))/2^k$, where the view of $s$ has at most $\sum_{j\le h}b^j$ entries. Because the view depends only on the residual graph and the query, recomputing a center returns the same value whatever the history or representation of its context.
--
--   Differences from the source:
--   - encoding: computing a center explores a constant-size neighborhood in its deletion computation tree → the center is a function of the depth-h preorder degree list, which has at most ∑_{j≤h} b^j entries; reason: the source's construction uses exactly this unfolding and no other graph data
--   - reading: constants depending only on Δ, λ, τ, and a deterministic computation → height, grid exponent and rule are one Computable family in the codes of Δ, λ, τ; reason: for fixed parameters the rule has finite domain and would be computable trivially; uniformity is the stronger reading, which the source's certified evaluation provides
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 9, printed p.7 (PDF p.8)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 9, printed p.7 (PDF p.8).
For fixed `Δ, λ, τ` there are a height `h`, a grid mesh `2^{-k}` and a rule `Φ`, computable
uniformly in the parameters, such that for every internal subproblem `s = (G - D, v)` the center
`c_s = Φ(view)/2^k` is a function of the depth-`h` unfolding of the deletion computation tree
alone; it lies in `[0,U]`, on the finite dyadic grid in `[0,Ū]`, within `τ` of `y_s`, and the
unfolding has at most `∑_{j ≤ h} b^j` nodes. -/
theorem deterministic_local_centers :
    ∃ (height gridExp : ℕ × RatCode × RatCode → ℕ)
      (rule : (ℕ × RatCode × RatCode) × List ℕ → ℕ),
      Computable height ∧ Computable gridExp ∧ Computable rule ∧
      ∀ (Delta : ℕ) (lam tau : ℚ), Standing Delta lam → 0 < tau →
        let key : ℕ × RatCode × RatCode := (Delta, codeOfRat lam, codeOfRat tau)
        ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V),
          MaxDegreeLE G Delta → ∀ (D : Finset V) (v : V), v ∉ D →
            residualDegree G D v ≤ bParam Delta →
            let view := deletionView G (height key) D v
            let cs : ℚ := (rule (key, view) : ℚ) / 2 ^ gridExp key
            (cs : ℝ) ≤ Umsg (lam : ℝ) ∧
            cs ≤ Ubar lam ∧
            |(cs : ℝ) - message G (lam : ℝ) D v| ≤ (tau : ℝ) ∧
            view.length ≤ ∑ j ∈ Finset.range (height key + 1), (bParam Delta) ^ j := by sorry

end HardCoreLocalSampling.Local
