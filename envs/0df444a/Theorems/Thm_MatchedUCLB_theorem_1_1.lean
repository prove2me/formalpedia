-- Prove2me | Theorems.Thm_MatchedUCLB_theorem_1_1
-- name    : MatchedUCLB.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:11.466992+00:00
-- url     : https://prove2.me/theorems/3da581ce-f5d3-4100-b1f8-c9e58b723e97
-- title:
--   Theorem 1.1 — matched-order lower bound: $\Omega_{p,\nu}((H/\sigma)^{2/(3q-2)}\log(\Delta_0/\epsilon))$ $p$th-order oracle calls
-- statement:
--   Fix an integer $p\ge2$, $0<\nu\le1$, and $q=p+\nu$. There are constants $c,K,\kappa_0,C>0$ depending only on $p,\nu$ such that the following holds. Let $H,\sigma,\Delta_0>0$ with $H/\sigma\ge\kappa_0$, let $0<\epsilon\le c\,\Delta_0$, and let the dimension satisfy
--
--   $$
--   d\ \ge\ K\Bigl(\frac H\sigma\Bigr)^{\frac{2}{3q-2}}\log\frac{\Delta_0}{\epsilon}.
--   $$
--
--   Then for every $x_0\in\mathbb R^d$ and every deterministic $p$th-order oracle algorithm there is a $p$ times continuously differentiable $F:\mathbb R^d\to\mathbb R$ with a minimizer $x_\star$ and $F(x_0)-F(x_\star)=\Delta_0$ such that, for all $x,y\in\mathbb R^d$,
--
--   1. **(a)** $\|\nabla^pF(y)-\nabla^pF(x)\|\le H\|y-x\|^\nu$;
--   2. **(b)** $F(y)\ge F(x)+\langle\nabla F(x),y-x\rangle+\frac\sigma q\|y-x\|^q$;
--
--   and, for every $T$, if the candidate $\hat x_T$ after $T$ oracle calls satisfies $F(\hat x_T)-F(x_\star)\le\epsilon$, then
--
--   $$
--   T\ \ge\ C\Bigl(\frac H\sigma\Bigr)^{\frac{2}{3q-2}}\log\frac{\Delta_0}{\epsilon}.
--   $$
--
--   This matches the upper bound $O_{p,\nu}\bigl((H/\sigma)^{2/(3q-2)}\log(\Delta_0/\epsilon)\bigr)$ of accelerated restarted $p$th-order methods, so it settles the complexity of the matched regime $q=p+\nu$, the case left open between the two asymmetric regimes.
--
--   **Formalization Note** The algorithm is quantified after $H,\sigma,\Delta_0,\epsilon,d$ and $x_0$, so it may depend on all of them; the hard function is chosen after the algorithm and before $T$.
--
--   Differences from the source:
--   - encoding: ℝ^d, ∇^kF, ⟨∇F(x), v⟩ → EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ k F, fderiv ℝ F x v; reason: Lean convention; the norm of iteratedFDeriv is the operator norm of Sec. 3; same instances
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - encoding: constants c_{p,ν}, K_{p,ν}; 'sufficiently large H/σ'; T ∈ Ω_{p,ν}(·) → ∃ c K κ₀ C > 0 before all other quantifiers; κ₀ ≤ H/σ; C·(H/σ)^{2/(3q−2)} log(Δ₀/ε) ≤ T; reason: the standard meaning of the asymptotic notation, with every constant depending only on p, ν
--   - encoding: deterministic pth-order oracle algorithm initialized at x_0 (Definition B.1) → A : OracleAlg d p (history maps of (F.1)–(F.2)) quantified after H, σ, Δ₀, ε, d, x₀; x̂_T = A.candPt F T; reason: any deterministic function of the parameters, the initialization and the history is a Lean function of the history once these are fixed
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Theorem 1.1, p.1

import Mathlib
import Definitions.Def_MatchedUCLB_HolderBound
import Definitions.Def_MatchedUCLB_UnifConvex
import Definitions.Def_MatchedUCLB_OracleAlg_candPt

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Theorem 1.1 (matched-order lower bound).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Theorem 1.1, p.1: "Fix an integer `p ≥ 2`,
`0 < ν ≤ 1`, and `q = p + ν`. There are constants `c_{p,ν}, K_{p,ν} > 0` such that, for `H, σ, Δ_0 > 0`
with sufficiently large `H/σ` and `0 < ε ≤ c_{p,ν}Δ_0`, and every dimension
`d ≥ K_{p,ν}(H/σ)^{2/(3q−2)} log(Δ_0/ε)`, every deterministic pth-order oracle algorithm initialized at
`x_0 ∈ ℝ^d` admits a `p` times continuously differentiable function `F : ℝ^d → ℝ` with minimizer `x⋆`
and `F(x_0) − F(x⋆) = Δ_0`, such that, for all `x, y ∈ ℝ^d`: (a) `‖∇^pF(y) − ∇^pF(x)‖ ≤ H‖y − x‖^ν`.
(b) `F(y) ≥ F(x) + ⟨∇F(x), y − x⟩ + (σ/q)‖y − x‖^q`. For a candidate `x̂_T` after `T` oracle calls,
`F(x̂_T) − F(x⋆) ≤ ε` requires `T ∈ Ω_{p,ν}((H/σ)^{2/(3q−2)} log(Δ_0/ε))`."

**Formalization Note.** `q` is a separate real binder with the hypothesis `q = p + ν` (the matched order of the paper), so that every formula can be written in `q`. `ℝ^d` is `EuclideanSpace ℝ (Fin d)`; `∇^kF` is `iteratedFDeriv ℝ k F`
(operator norm, Sec. 3). "Sufficiently large `H/σ`" is a threshold `κ₀ ≤ H/σ`, and
`T ∈ Ω_{p,ν}(·)` is `C·(H/σ)^{2/(3q−2)} log(Δ_0/ε) ≤ T` for a constant `C > 0`; `c, K, κ₀, C` are
chosen before every other quantifier and depend only on `p, ν`. The algorithm is `A : OracleAlg d p`
(Definition B.1, (F.1)–(F.2)), quantified after `H, σ, Δ_0, ε, d, x_0`, so it may depend on all of
them; `x̂_T = A.candPt F T`. `F` is chosen after the algorithm and before `T`, and the call bound
holds for every `T`. -/
theorem theorem_1_1 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) :
    ∃ c K κ₀ C : ℝ, 0 < c ∧ 0 < K ∧ 0 < κ₀ ∧ 0 < C ∧
      ∀ H σ Δ₀ ε : ℝ, 0 < H → 0 < σ → 0 < Δ₀ → κ₀ ≤ H / σ → 0 < ε → ε ≤ c * Δ₀ →
      ∀ d : ℕ, K * (H / σ) ^ (2 / (3 * q - 2)) * Real.log (Δ₀ / ε) ≤ d →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (A : OracleAlg d p),
      ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ p F ∧ HolderBound p ν H F ∧ UnifConvex q σ F ∧
        ∃ xs : EuclideanSpace ℝ (Fin d), (∀ y : EuclideanSpace ℝ (Fin d), F xs ≤ F y) ∧ F x₀ - F xs = Δ₀ ∧
          ∀ T : ℕ, F (A.candPt F T) - F xs ≤ ε →
            C * (H / σ) ^ (2 / (3 * q - 2)) * Real.log (Δ₀ / ε) ≤ T := by sorry

end MatchedUCLB
