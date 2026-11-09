-- Prove2me | Theorems.Thm_LocalPush_lemma_5_2
-- name    : LocalPush.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:46.193705+00:00
-- url     : https://prove2.me/theorems/c6c268a9-ff4e-462a-a748-c8f209aee6fb
-- title:
--   Lemma 5.2 — entrywise error bounds (14)–(16) after one solve satisfying (6)
-- statement:
--   Assume the parameters of Algorithm 3: $\alpha\in(0,1)$, $\lambda,\eta>0$, $0<\kappa\le0.4\alpha\eta^2$, $\mu=0.01\alpha\min\{\lambda,\kappa\}$, and $(\lambda+\eta)d(s)<1$, on a graph without isolated nodes. Let $S\ni s$ satisfy $x^{(S)}\ge0$, and let $\tilde x$ vanish outside $S$ with $\tilde x_S$ satisfying (6) for the system $L_{\alpha,S}x_S=\alpha(e_s|_S-\lambda d_S)$. With $\tilde r:=r(\tilde x)$,
--   $$|\tilde r(v)-\lambda d(v)|\le0.1\min\{\lambda,\kappa\}\,d(v)\quad\forall v\in S,\tag{14}$$
--   $$|\tilde x(v)-x^{(S)}(v)|\le0.1\alpha\kappa\quad\forall v\in S,\tag{15}$$
--   $$|\tilde r(v)-r(x^{(S)})(v)|\le0.1\kappa\,d(v)\quad\forall v\in\partial S.\tag{16}$$
--
--   These bounds transfer the exact-state analysis to the approximate solver outputs.
--
--   Differences from the source:
--   - generalization: 𝒮 is the active set of an iteration of Algorithm 3 → any set S containing s with x^(S) ≥ 0; reason: the proof (§A.2) uses only s ∈ S, x^(S) ≥ 0, the parameters and (6); every active set of an iteration is such a set
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.2 (proof §A.2, pp.55–56), p.19 (PDF p.19)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.2 (entrywise error of one successful approximate solve).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.2, p.19 (PDF p.19);
proof in §A.2, pp.55–56.

"Suppose that (λ + η)d(s) < 1 and in an iteration of Algorithm 3, the set 𝒮 satisfies x^(𝒮) ≥ 0. Suppose that
the approximate SDD solve in this iteration returns a x̃_𝒮 satisfying the guarantee (6). Extend x̃_𝒮 to
x̃ ∈ ℝ^V by setting x̃_{V∖𝒮} := 0, and let r̃ := r(x̃). Then
|r̃(v) − λd(v)| ≤ 0.1 min{λ, κ} d(v), ∀ v ∈ 𝒮, (14)
|x̃_𝒮(v) − x^(𝒮)(v)| ≤ 0.1ακ, ∀ v ∈ 𝒮, (15)
|r̃(v) − r(x^(𝒮))(v)| ≤ 0.1κ d(v), ∀ v ∈ ∂𝒮. (16)"

Under the parameters of Algorithm 3 (`Params`, which includes `(λ + η)d(s) < 1`), for every set `S ∋ s` with
`x^(S) ≥ 0` and every `x̃` vanishing outside `S` whose restriction satisfies (6) for the system of line 6
(`SolveGood`, with `µ = 0.01α min{λ, κ}`), the three two-sided bounds hold with `r̃ = r(x̃)`.

**Formalization Note.** `S` is any set containing `s` with `x^(S) ≥ 0`; it need not be an active set the
algorithm reaches. -/
theorem lemma_5_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (S : Finset V) (hs : s ∈ S) (hx : ∀ v, 0 ≤ xS G s α lam S v)
    (xt : V → ℝ) (hxt : ∀ v ∉ S, xt v = 0) (hsolve : SolveGood G s α lam κ S xt) :
    (∀ v ∈ S, |resid G α s xt v - lam * deg G v| ≤ 0.1 * min lam κ * deg G v) ∧
    (∀ v ∈ S, |xt v - xS G s α lam S v| ≤ 0.1 * α * κ) ∧
    (∀ v ∈ bdry G S, |resid G α s xt v - resid G α s (xS G s α lam S) v| ≤ 0.1 * κ * deg G v) := by sorry

end LocalPush
