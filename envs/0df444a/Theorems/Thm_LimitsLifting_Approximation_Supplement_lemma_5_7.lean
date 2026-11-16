-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_Supplement_lemma_5_7
-- name    : LimitsLifting.Approximation.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:34:31.056864+00:00
-- url     : https://prove2.me/theorems/8dbe2342-5eff-4763-88b0-17be9450341f
-- title:
--   Lemma 5.7 — random approximators are dominated by random error sets
-- statement:
--   Let $\mathcal M$ be a legitimate model over $Z_n\subseteq\{0,1\}^n$ of Boolean circuits over $\{\vee_2,\wedge_2\}$, with error-set family $\Delta$. Let $\ell\in[n-1]$, i.e. $1\le\ell\le n-1$, and let $f\in\mathcal F_n$ be an $\ell$-slice, a Boolean function on the whole cube $\{0,1\}^n$. Let $n_0$ be the number of essential inputs of $f$ and
--
--   $$\Gamma=12\big(3(n_0+1)+\tilde t_{\ell,n_0}+t_{\ell,n_0}+t_{\ell+1,n_0}+2\big).$$
--
--   Then there are a random error set $\boldsymbol\delta$ taking values in $\Delta$ and a random function $\boldsymbol h$ taking values in $\mathcal M$ such that, simultaneously for every $x\in Z_n$,
--
--   $$\mathbb P[\boldsymbol h(x)\neq f(x)]\le\Gamma\,\mathbb P[x\in\boldsymbol\delta].$$
--
--   The two laws are fixed before $x$. Averaging this inequality over a random input gives the probabilistic part of the approximation barrier for slices (Theorem 5.6), and sampling from both laws gives its general part.
--
--   **Formalization Note** The random variables are probability mass functions on the finite types of subsets of $Z_n$ and of functions $Z_n\to\{0,1\}$, with supports contained in $\Delta$ and in $\mathcal M$; probabilities are in `ℝ≥0∞`. The slice condition is imposed on the whole cube, and $f$ is compared with $\boldsymbol h$ on $Z_n$.
--
--   Differences from the source:
--   - generalization: $\tilde t_{\ell,n_0}$, $t_{\ell,n_0}$, $t_{\ell+1,n_0}$ are the sizes of fixed monotone threshold circuits (all gates counted) → the minimum number of binary ∧/∨ gates of a monotone circuit (shared gates counted once) computing the same functions; reason: each minimum is at most the size of any fixed circuit, so the Lean $\Gamma$ is at most the printed one and the Lean inequality implies the printed one for every choice of circuits
--   - encoding: random variables $\boldsymbol\delta$ on $\Delta$ and $\boldsymbol h$ on $\mathcal M$ → probability mass functions on `Set Z` and `Z → Bool` with support in $\Delta$ and $\mathcal M$; reason: same objects on finite types
--   - encoding: $f\in\mathcal F_n$, an $\ell$-slice, $\ell\in[n-1]$ → a total `f : (Fin n → Bool) → Bool` satisfying the slice condition on all of $\{0,1\}^n$, with `1 ≤ ℓ` and `ℓ ≤ n - 1`, and $n_0$ the essential-input count of this total function; reason: $\mathcal F_n=\mathcal F(\{0,1\}^n)$ in the proof; inputs indexed by `Fin n`
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Lemma 5.7, printed p. 28 (PDF p. 29); Γ defined in the proof of Theorem 5.6, printed p. 28 (PDF p. 29); proof printed pp. 29–31 (PDF pp. 30–32).

import Mathlib
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_Supplement_SliceBarrier
open Classical
open scoped ENNReal
open LimitsLifting.Approximation

namespace LimitsLifting.Approximation.Supplement

/-- Carenini–Cavalar–Grosser–Pich, *Limits of Lifting*, Lemma 5.7 (printed p. 28, PDF p. 29).
For every legitimate model `A` over `Z ⊆ {0,1}ⁿ` of circuits over `{∨₂, ∧₂}`, every `ℓ ∈ [n-1]`
and every total `ℓ`-slice `f ∈ Fₙ = F({0,1}ⁿ)`, there are a random error set `δ` (law `pδ`,
supported on `Δ`) and a random model function `h` (law `ph`, supported on `M`) such that for
every `x ∈ Z`, `P[h(x) ≠ f(x)] ≤ Γ · P[x ∈ δ]`, where
`Γ = 12(3(n₀+1) + t̃_{ℓ,n₀} + t_{ℓ,n₀} + t_{ℓ+1,n₀} + 2)` and `n₀` is the number of essential
inputs of `f`. -/
theorem lemma_5_7 (n : ℕ) (Z : Set (Fin n → Bool)) (A : ApproxModel Z) (ℓ : ℕ)
    (hℓ₁ : 1 ≤ ℓ) (hℓ₂ : ℓ ≤ n - 1) (f : (Fin n → Bool) → Bool)
    (hf : IsSlice ℓ (fun z : (Set.univ : Set (Fin n → Bool)) => f z.1)) :
    ∃ (pδ : PMF (Set Z)) (ph : PMF (Z → Bool)),
      pδ.support ⊆ errorSets A ∧ ph.support ⊆ A.M ∧
      ∀ x : Z, ph.toOuterMeasure {h | h x ≠ f x.1} ≤
        (Gamma ℓ (essentialCount (fun z : (Set.univ : Set (Fin n → Bool)) => f z.1)) : ℝ≥0∞) *
          pδ.toOuterMeasure {E | x ∈ E} := by sorry

end LimitsLifting.Approximation.Supplement
