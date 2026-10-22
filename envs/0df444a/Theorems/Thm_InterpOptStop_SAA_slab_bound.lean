-- Prove2me | Theorems.Thm_InterpOptStop_SAA_slab_bound
-- name    : InterpOptStop.SAA.slab_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:40.92827+00:00
-- url     : https://prove2.me/theorems/b5d5d99f-91ed-4b82-a27e-a1d1e2f1b51d
-- title:
--   Proof of Lemma EC.2, p. ec3 — Pr[x_{v(s)}(t) ∈ [min{θ1s,θ2s}, max{θ1s,θ2s}]] ≤ f(|θ1s − θ2s|)
-- statement:
--   Let the state space $\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n\subseteq\mathbb R^n$ be totally bounded with $\|\mathbf x-\mathbf y\|_\infty\le1$ for all $\mathbf x,\mathbf y\in\mathcal X$ (Assumption 1). Let the path $(\mathbf x(1),\dots,\mathbf x(T))$ have law $\mu$ and lie in $\mathcal X$ almost surely. Suppose $f:[0,\infty)\to\mathbb R$ satisfies $f(0)=0$, is strictly increasing and continuous, and
--   $$\Pr[\mathbf x(t)\in A]\le f(\lambda(A))$$
--   for every measurable $A\subseteq\mathbb R^n$ of finite Lebesgue measure $\lambda(A)$ and every period $1<t\le T$ (Assumption 3). Then for every period $1<t\le T$, every coordinate $i$ and all reals $a,b$,
--   $$\Pr\big[x_i(t)\in[\min\{a,b\},\max\{a,b\}]\big]\le f(|a-b|).$$
--
--   This is the probabilistic estimate behind Lemma EC.2 and term (c) of Lemma EC.1: a threshold moved from $a$ to $b$ changes the decision of a split only on an event of probability at most $f(|a-b|)$.
--
--   **Formalization Note** Periods are 0-indexed (`k : Fin T`, $t=k+1$, so $t>1$ is `k ≠ 0`). The slab is `Set.uIcc a b`. Assumption 3 is used for measurable sets of finite Lebesgue measure, the only sets for which $f(\mu(A))$ and $\Pr[\cdot]$ are meaningful on the page. The paper states $f:[0,\infty)\to[0,1]$. With that codomain Assumption 3 cannot hold whenever $n\ge1$ and $T\ge2$, because a box containing the bounded set $\mathcal X$ has probability $1$, which forces $f\equiv1$ on a half-line. The codomain is therefore dropped. This loses nothing: for a $[0,1]$-valued $f$ satisfying the other conditions, $r\mapsto f(r)+r$ satisfies them too and dominates $f$. The authors' own example, densities bounded by $c$ with $f(r)=cr$, is of this unbounded kind.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, proof of Lemma EC.2, last display, p. ec3; Assumptions 1 and 3, p. 9

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Proof of Lemma EC.2, last display (arXiv:1812.07211v2, p. ec3): under Assumptions 1 and 3,
for every period `t = k + 1 > 1`, coordinate `i` and reals `a, b`,
`Pr[x_i(t) ∈ [min{a,b}, max{a,b}]] ≤ f(|a − b|)`. -/
theorem slab_bound {n T : ℕ}
    (hT : 0 < T)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (hXtb : TotallyBounded X) (hXdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ 1)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousOn f (Set.Ici 0))
    (hA3 : ∀ A : Set (Fin n → ℝ), MeasurableSet A → volume A ≠ ⊤ →
      ∀ k : Fin T, (k : ℕ) ≠ 0 → (μ {x | x k ∈ A}).toReal ≤ f (volume A).toReal) :
    ∀ k : Fin T, (k : ℕ) ≠ 0 → ∀ (i : Fin n) (a b : ℝ),
      (μ {x | x k i ∈ Set.uIcc a b}).toReal ≤ f |a - b| := by sorry

end InterpOptStop.SAA
