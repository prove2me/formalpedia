-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_snell_envelope_largest
-- name    : MultiperiodRisk.Bellman.snell_envelope_largest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:03:58.017649+00:00
-- url     : https://prove2.me/theorems/3dc60848-f2f1-4d16-ab0d-e41180450dcd
-- title:
--   Theorem 4.1 — $\bar\Psi(X)$ is the largest process below $X$ that is a $\mathbb Q$-submartingale for every $\mathbb Q\in\mathcal P$
-- statement:
--   Let $\mathcal P$ be a closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, with $\mathcal P^e\ne\emptyset$, and let $X$ be a value process. Let $\bar\Psi(X)$ be given by
--   $$
--   \bar\Psi_N(X)=X_N,\qquad \bar\Psi_n(X)=X_n\wedge\operatorname*{ess.inf}_{\mathbb Q\in\mathcal P^e}\mathbb E_{\mathbb Q}\bigl[\bar\Psi_{n+1}(X)\mid\mathcal F_n\bigr]\quad(0\le n<N).
--   $$
--   Then:
--
--   1. $\bar\Psi(X)$ is a value process;
--   2. $\bar\Psi_n(X)\le X_n$ a.s. for $0\le n\le N$;
--   3. for every $\mathbb Q\in\mathcal P$, $\bar\Psi(X)$ is a $\mathbb Q$-submartingale on $0,\dots,N$;
--   4. every value process $Y$ with $Y_n\le X_n$ a.s. for $n\le N$ that is a $\mathbb Q$-submartingale for every $\mathbb Q\in\mathcal P$ satisfies $Y_n\le\bar\Psi_n(X)$ a.s. for $n\le N$.
--
--   So $\bar\Psi(X)$ is the largest process in $\mathcal G$ below $X$ with the submartingale property under every test probability, and it is unique up to null sets. It is a generalized Snell envelope and serves as the benchmark against which $\Psi$ is compared in Theorem 4.2.
--
--   **Formalization Note** A $\mathbb Q$-submartingale on $0,\dots,N$ is expressed as Mathlib's `Submartingale` for the process frozen after time $N$, under the measure $\mathbb Q_f=f\cdot\mathbb P_0$ for each density $f\in D$ (including those not equivalent to $\mathbb P_0$). Uniqueness follows from the maximality statement and is not a separate conjunct. The hypothesis $\mathcal P^e\ne\emptyset$ comes from the paper's standing convention $\mathbb P_0\in\mathcal P$ (p. 9) and is weaker than it.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, Theorem 4.1

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Theorem 4.1: `Ψ̄(X)` is a value process below `X`, a `ℚ`-submartingale on `0, …, N`
for every `ℚ ∈ 𝒫`, and the largest such process. -/
theorem snell_envelope_largest {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X) :
    IsValueProcess P₀ ℱ N (PsiBar D X) ∧
    (∀ n ≤ N, PsiBar D X n ≤ᵐ[P₀] X n) ∧
    (∀ f ∈ D.set, Submartingale (fun n => PsiBar D X (min n N)) ℱ (Q P₀ f)) ∧
    (∀ Y : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N Y → (∀ n ≤ N, Y n ≤ᵐ[P₀] X n) →
      (∀ f ∈ D.set, Submartingale (fun n => Y (min n N)) ℱ (Q P₀ f)) →
      ∀ n ≤ N, Y n ≤ᵐ[P₀] PsiBar D X n) := by sorry

end MultiperiodRisk.Bellman
