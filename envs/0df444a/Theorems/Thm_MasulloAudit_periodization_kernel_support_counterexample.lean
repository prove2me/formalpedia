-- Prove2me | Theorems.Thm_MasulloAudit_periodization_kernel_support_counterexample
-- name    : MasulloAudit.periodization_kernel_support_counterexample
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:15:54.878171+00:00
-- url     : https://prove2.me/theorems/9f47d320-315b-4a04-9510-649936b4e39f
-- title:
--   Proposition 4.2.2.2(2) as printed fails: the solution of $\psi(x)-\psi(\gamma x)=\varphi(x)$ is not supported in $[e^{-A},e^{A}]$
-- statement:
--   **Context.** For a real number $\gamma>1$, Masullo's manuscript studies the periodization operator $\Phi_\gamma(\varphi)(x)=\sum_{k\in\mathbf Z}\varphi(\gamma^k x)$ on functions on $\mathbf R_{>0}$, and for a compact $K\subset\mathbf R_{>0}$ the space $\mathcal D_K(\mathbf R_{>0})$ of smooth functions supported in $K$. Proposition 4.2.2.2(2) (p. 171) states:
--
--   > Assume $K=b\cdot[1/a,a]$ for real numbers $a,b>0$, $a>1$ [with $K$ mapping onto $\mathbf R_{>0}/\gamma^{\mathbf Z}$, e.g. $2\log a>\log\gamma$]. Let $\varphi\in\ker(\Phi_\gamma)\cap\mathcal D_K(\mathbf R_{>0})$. Let $A_0>0$ be a real number such that $K\subset[1/A_0,A_0]$, and define $A:=|-\log\gamma+\log A_0|$ and $K_A:=[e^{-A},e^{A}]$. There exists $\psi\in\mathcal D_{K_A}(\mathbf R_{>0})$ such that $\psi(x)-\psi(\gamma x)=\varphi(x)$.
--
--   **Statement (refutes the printed proposition).** Let $\gamma>1$, $a>1$ with $a^2>\gamma$ (so that $K=[1/a,a]$, i.e. $b=1$, satisfies the surjectivity assumption), and let $A_0$ be any real number with $a\le A_0<a\gamma$ (so $K\subset[1/A_0,A_0]$; the choice $A_0=a$ is the one made in the manuscript's proof). Put $A=|\log A_0-\log\gamma|$. Then there is a smooth function $\varphi:\mathbf R\to\mathbf C$ with
--
--   * $\operatorname{supp}\varphi\subset[1/a,a]$, and
--   * $\sum_{k\in\mathbf Z}\varphi(\gamma^k x)=0$ for every $x>0$ (the family is summable; in fact only finitely many terms are nonzero),
--
--   such that **no** function $\psi:\mathbf R\to\mathbf C$ whatsoever (no smoothness or continuity is required) that vanishes outside $K_A=[e^{-A},e^{A}]$ satisfies $\psi(x)-\psi(\gamma x)=\varphi(x)$ for all $x>0$.
--
--   For instance, for $a=A_0=\gamma$ one has $A=0$ and $K_A=\{1\}$, so the printed statement would force every $\varphi\in\ker(\Phi_\gamma)\cap\mathcal D_{[1/\gamma,\gamma]}(\mathbf R_{>0})$ to vanish, which is false.
--
--   **Relation to the source.** This is a counterexample to the exact printed statement of Proposition 4.2.2.2(2), for $b=1$, every admissible $a$, and every $A_0\in[a,a\gamma)$ (for $A_0\ge a\gamma$ the printed support claim is correct, since then $K_A\supset[\gamma/a,a]$). The error in the printed proof is the two-sided estimate (4.2.2.6): dividing the Mellin transform by $1-\gamma^{-s}$ improves the exponential type only as $\operatorname{Re}(s)\to-\infty$, not as $\operatorname{Re}(s)\to+\infty$. The compactly supported solution is unique, $\psi(x)=\sum_{k\ge0}\varphi(\gamma^kx)$, and its support lies in $[\gamma/a,\,a]$, which is not contained in $[e^{-A},e^{A}]$ in the stated range. The statement says nothing about the Riemann Hypothesis; it concerns the support bookkeeping used in Proposition 4.2.2.5 (p. 173).
--
--   **Formalization notes.** Functions on $\mathbf R_{>0}$ are represented as functions on $\mathbf R$ supported in $(0,\infty)$; `ContDiff ℝ ∞ φ` is $C^\infty$-smoothness, `Function.support φ ⊆ Set.Icc a⁻¹ a` is the support condition (the interval is closed, so this is the same as a condition on the closed support), and the kernel condition is stated with `HasSum` over $k\in\mathbf Z$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Proposition 4.2.2.2(2), p. 171 (proof on pp. 172-173, estimate (4.2.2.6)); used in Proposition 4.2.2.5, p. 173

import Mathlib

set_option autoImplicit false

open scoped ContDiff

namespace MasulloAudit

/-- Counterexample to Masullo, Proposition 4.2.2.2(2) (p. 171). For `γ > 1`, `K = [1/a, a]` with
`a > 1`, `a² > γ`, and any `A₀` with `a ≤ A₀ < aγ` (so `K ⊆ [1/A₀, A₀]`), put
`A = |log A₀ - log γ|`. There is a smooth `φ` supported in `K` whose `γ^ℤ`-periodization
`∑_k φ(γ^k x)` vanishes on `(0, ∞)`, but no function `ψ` at all (no regularity required) that
vanishes outside `K_A = [e^{-A}, e^{A}]` solves `ψ(x) - ψ(γx) = φ(x)` on `(0, ∞)`. -/
theorem periodization_kernel_support_counterexample (γ a A₀ : ℝ) (hγ : 1 < γ) (ha : 1 < a)
    (haγ : γ < a ^ 2) (hA₀ : a ≤ A₀) (hA₀' : A₀ < a * γ) :
    ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ Function.support φ ⊆ Set.Icc a⁻¹ a ∧
      (∀ x : ℝ, 0 < x → HasSum (fun k : ℤ => φ (γ ^ k * x)) 0) ∧
      ¬ ∃ ψ : ℝ → ℂ,
        Function.support ψ ⊆ Set.Icc (Real.exp (-|Real.log A₀ - Real.log γ|))
          (Real.exp |Real.log A₀ - Real.log γ|) ∧
        ∀ x : ℝ, 0 < x → ψ x - ψ (γ * x) = φ x := by sorry

end MasulloAudit
