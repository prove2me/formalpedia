-- Prove2me | Theorems.Thm_LimitedPersuasion_theorem_1
-- name    : LimitedPersuasion.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:57.18631+00:00
-- url     : https://prove2.me/theorems/0f8b2060-507f-44b6-9505-6c437bb2f497
-- title:
--   Theorem 1 — in every symmetric instance some optimal $k$-signal scheme has recommendation points forming a sender-optimal $s$-Pareto collection
-- statement:
--   Let $2\le k\le n$ and consider a symmetric instance with distinct types: a prior $q$ on states $\boldsymbol\theta\in T^n$ over a finite type set $T$, invariant under permutations of the $n$ actions, with arbitrary values $\varrho,\xi:T\to\mathbb R$. The receiver best responds to each signal and breaks ties in favour of the sender. Then there are a $k$-signal scheme $\varphi$ and a slope $s$ such that
--
--   1. $\varphi$ is optimal: $u_S(\varphi)\ge u_S(\psi)$ for every $k$-signal scheme $\psi$;
--   2. $\varphi$ is direct and persuasive, with signal $j$ recommending action $j\in[k]$, and the sender's utility under the receiver's tie-broken best response equals the utility when the receiver follows the recommendation;
--   3. the recommendation points of $\varphi$ form an $s$-Pareto point collection $\mathcal P(\varphi)$ (in particular $s\le 0$);
--   4. $\mathcal P(\varphi)$ is sender-optimal over all slopes: for every $s'$ and every $s'$-Pareto point collection $\mathcal P'$,
--   $$u_S(\mathcal P')\ \le\ u_S(\mathcal P(\varphi)).$$
--
--   Thus optimal signaling with $k<n$ messages in symmetric instances reduces to choosing a common slope $s$ and one point on each Pareto frontier, which is the basis of the paper's polynomial-time Slope-Algorithm.
--
--   **Formalization Note** $n\ge1$ is assumed as a typeclass fact; it follows from $2\le k\le n$.
--
--   Differences from the source:
--   - reading: "optimal scheme" → `IsOptimal`, optimal against every $k$-signal scheme with the tie-broken best-response utility $u_S$; reason: the paper's definition (§2, pp.4–5), made explicit
--   - reading: "sender-optimal $s$-Pareto point collection, over all $s\le0$" → $u_S(\mathcal P')\le u_S(\mathcal P(\varphi))$ for every $s'$ and every $s'$-Pareto $\mathcal P'$; reason: the plain meaning; $s'$-Pareto includes $s'\le0$
--   - generalization: recommendation points presuppose a direct scheme recommending from $[k]$ → clause 2 asserts it, with persuasiveness and $u_S$ equal to the follow utility; reason: a stronger conclusion that the paper's proof provides (Lemmas 1, 3, 4) and that implies the printed statement
--   - reading: Definition 1's conditions for every $C$, frontier and slope defined graphically → for every $C$ with $q_C\ne0$; frontier: no hull point strictly larger in both coordinates (keeps the horizontal and vertical end segments of p.6); slope: real $s\le0$ with the supporting-line inequality on the hull; reason: recommendation points exist only where $q_C>0$; dropping null $C$ lets clause 4 quantify over more collections; slope $-\infty$ is not in Definition 1 ("For $s\le0$"; §3.2 uses $[0,-\infty)$)
--   - reading: recommendation point $(\mathbb E[u_R(\varphi)\mid C],\mathbb E[u_S(\varphi)\mid C])$ → computed with the receiver following the recommendation; reason: §3's utilities of a direct scheme
--   - encoding: type sets $\Theta_i$, signals $\Sigma$ with $|\Sigma|=k$ → one finite type set $T$, states $\mathrm{Fin}\,n\to T$, signals $\mathrm{Fin}\,k$, prior a weight function, $n\ge1$ as an instance; reason: Lean convention, same instances
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, Theorem 1, §3.1, p.6 (proof pp.6–8)

import Mathlib
import Definitions.Def_LimitedPersuasion_PointCollection

namespace LimitedPersuasion

/-- **Theorem 1**, Gradwohl–Hahn–Hoefer–Smorodinsky, *Algorithms for Persuasion with Limited
Communication*, arXiv:2007.12489v2, §3.1, p.6: for every symmetric instance, there is an optimal
scheme whose recommendation points are a sender-optimal `s`-Pareto point collection, over all
`s ≤ 0`.

Precisely: for every symmetric instance with distinct types and every `2 ≤ k ≤ n`, there are a
`k`-signal scheme `φ` and a slope `s` such that

1. `φ` is optimal among all `k`-signal schemes (best response with sender-favourable ties);
2. `φ` is direct and persuasive, recommending action `j ∈ [k]` with signal `j`, and the
   receiver's tie-broken best response yields the sender the recommendation's value;
3. the recommendation points of `φ` form an `s`-Pareto point collection (in particular `s ≤ 0`);
4. no `s'`-Pareto point collection, for any `s' ≤ 0`, gives the sender a larger utility.

**Formalization Note.** `[NeZero n]` follows from `2 ≤ k ≤ n`. Recommendation points are only
evaluated on sets `C` with `q_C ≠ 0`. -/
theorem theorem_1 {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ} [NeZero n]
    (I : Instance T n) (hk : 2 ≤ k) (hkn : k ≤ n) (hsym : I.IsSymmetric)
    (hdist : I.DistinctTypes) :
    ∃ (φ : (Fin n → T) → Fin k → ℝ) (s : ℝ),
      I.IsOptimal φ ∧
      I.Persuasive φ (Fin.castLE hkn) ∧ I.uS φ = I.followS φ (Fin.castLE hkn) ∧
      I.IsSPareto hkn s (I.recPt hkn φ) ∧
      ∀ (s' : ℝ) (P' : Finset T → ℝ × ℝ),
        I.IsSPareto hkn s' P' → I.uSP hkn P' ≤ I.uSP hkn (I.recPt hkn φ) := by sorry

end LimitedPersuasion
