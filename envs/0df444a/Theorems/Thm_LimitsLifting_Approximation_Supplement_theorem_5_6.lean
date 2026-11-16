-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_Supplement_theorem_5_6
-- name    : LimitsLifting.Approximation.Supplement.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:35:02.633224+00:00
-- url     : https://prove2.me/theorems/c888e2df-6303-45f2-aa21-85d8593f3e36
-- title:
--   Theorem 5.6 — approximation barrier for slices
-- statement:
--   There are absolute constants $C_{\mathrm{gen}},C_{\mathrm{prob}}>0$ with the following property. Let $n\ge0$, let $Z_n\subseteq\{0,1\}^n$ be arbitrary, let $\mathcal M$ be a legitimate model over $Z_n$ of Boolean circuits over $\{\vee_2,\wedge_2\}$, let $\ell\in[n-1]$, and let $f\in\mathcal F(Z_n)$ be an $\ell$-slice. Let $n_0$ be the number of essential inputs of $f$: inputs such that switching their value changes the output of $f$ (where $f$ takes the value $\star$ outside $Z_n$) on some assignment of the remaining inputs. Then
--
--   $$\rho(f,\mathcal M)\le C_{\mathrm{gen}}\,\big(n_0+\tilde t_{\ell,n_0}\big)\,n,$$
--
--   and for every random variable $x$ on $Z_n$,
--
--   $$\rho(f,\mathcal M,x)\le C_{\mathrm{prob}}\,\big(n_0+\tilde t_{\ell,n_0}\big).$$
--
--   Here $\rho(f,\mathcal M)$ is Razborov's distance (the least number of error sets covering $f\oplus g$ for some $g\in\mathcal M$), $\rho(f,\mathcal M,x)$ is the probabilistic distance, and $\tilde t_{\ell,k}$ is the size of a monotone $k$-input $k$-output circuit computing all the thresholds $T^{k-1}_\ell(X_i)$.
--
--   By Proposition 5.5, $\rho(f,\mathcal M)$ is a lower bound on circuit size; the theorem says that, for slice functions, the approximation method (in its general and its probabilistic form) cannot prove monotone circuit lower bounds larger than about $n\cdot n_0\log^2 n_0$. It is a companion result of the paper and is not used in the proof of the mission's goal.
--
--   **Formalization Note** $\rho(f,\mathcal M)$ is a value in `ℕ∞` cast to `ℝ≥0∞`, so an infinite distance violates the bound; $\rho(f,\mathcal M,x)$ is in `ℝ≥0∞`, and the law of $x$ is a probability mass function on $Z_n$. Both bounds are compared with `ENNReal.ofReal` of the real right-hand side.
--
--   Differences from the source:
--   - reading: $\rho(f,\mathcal M)\le O((n_0+\tilde t_{\ell,n_0})n)$ and $\rho(f,\mathcal M,x)\le O(n_0+\tilde t_{\ell,n_0})$ → there exist $C_{\mathrm{gen}},C_{\mathrm{prob}}>0$, chosen before $n$, $Z_n$, $\mathcal M$, $\ell$, $f$ and the law of $x$, with both inequalities for every instance; reason: the uniform reading of the O-bounds, with no per-instance constant and no size threshold
--   - generalization: $\tilde t_{\ell,n_0}$ is the size of a fixed shared threshold network (all gates counted) → the minimum number of binary ∧/∨ gates of a monotone $n_0$-input $n_0$-output circuit computing $(T^{n_0-1}_\ell(X_i))_i$, shared gates counted once; reason: the minimum is at most the size of any fixed network, so the Lean bounds imply the printed ones for every choice of network
--   - reading: essential inputs of a partial $f$ → input $i$ is essential iff switching $x_i$ changes $\hat f\in\{0,1,\star\}$ ($\star$ off $Z_n$) at some point; reason: §2.1's partial-map convention; requiring both points in $Z_n$ makes the statement false: for $Z_n$ the weight-$\ell$ layer and $\mathcal M=\{0,1,x_1,\dots,x_n\}$ with $g\mathbin{\bar\wedge}h=g\mathbin{\bar\vee}h=0$, that reading gives $n_0=0$, a bound $0$, yet $f$ can differ from every member of $\mathcal M$
--   - reading: $\tilde t_{\ell,n_0}$ when $\ell\ge n_0$ or $n_0=0$ → the same minimum, which is $0$ (constant outputs, or no outputs); reason: the definition applies literally; the source excludes no such case
--   - encoding: $\rho(f,\mathcal M)\in\mathbb N\cup\{\infty\}$, $\rho(f,\mathcal M,x)\in\mathbb R_{\ge0}$, a random variable $x$ on $Z_n$ → `ℕ∞` cast to `ℝ≥0∞`, `ℝ≥0∞` with the printed $d=0$ convention, a `PMF` on $Z_n$; reason: the same values on finite domains
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Theorem 5.6 (Approximation barrier for slices), printed p. 28 (PDF p. 29), with footnote 6; informal restatement Theorem 1.4, printed p. 4 (PDF p. 5); proof printed pp. 28–31 (PDF pp. 29–32).

import Mathlib
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_Supplement_SliceBarrier
open Classical
open scoped ENNReal
open LimitsLifting.Approximation

namespace LimitsLifting.Approximation.Supplement

/-- Carenini–Cavalar–Grosser–Pich, *Limits of Lifting*, Theorem 5.6, Approximation barrier for
slices (printed p. 28, PDF p. 29; informal Theorem 1.4). There are absolute constants
`C_gen, C_prob > 0` such that for every `n`, every `Z ⊆ {0,1}ⁿ`, every legitimate model `A` over
`Z` of circuits over `{∨₂, ∧₂}`, every `ℓ ∈ [n-1]` and every `ℓ`-slice `f ∈ F(Z)`, with `n₀` the
number of essential inputs of `f`:
`ρ(f, M) ≤ C_gen (n₀ + t̃_{ℓ,n₀}) n`, and `ρ(f, M, x) ≤ C_prob (n₀ + t̃_{ℓ,n₀})` for every law
`ν` of a random input `x` on `Z`. -/
theorem theorem_5_6 :
    ∃ C_gen C_prob : ℝ, 0 < C_gen ∧ 0 < C_prob ∧
      ∀ (n : ℕ) (Z : Set (Fin n → Bool)) (A : ApproxModel Z) (ℓ : ℕ) (f : Z → Bool),
        1 ≤ ℓ → ℓ ≤ n - 1 → IsSlice ℓ f →
          ((distGen A f : ℝ≥0∞) ≤
              ENNReal.ofReal (C_gen *
                ((essentialCount f : ℝ) + (sharedThresholdSize ℓ (essentialCount f) : ℝ)) *
                (n : ℝ))) ∧
          ∀ ν : PMF Z, distProb A f ν ≤
            ENNReal.ofReal (C_prob *
              ((essentialCount f : ℝ) + (sharedThresholdSize ℓ (essentialCount f) : ℝ))) := by sorry

end LimitsLifting.Approximation.Supplement
