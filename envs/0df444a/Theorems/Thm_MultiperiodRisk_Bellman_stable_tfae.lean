-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_stable_tfae
-- name    : MultiperiodRisk.Bellman.stable_tfae
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:08:05.012626+00:00
-- url     : https://prove2.me/theorems/0f54f789-b916-446e-b23c-a2cb75053924
-- title:
--   Theorem 4.2 — stability of $\mathcal P$ $\iff$ submartingale property $\iff$ $\Psi=\bar\Psi$ $\iff$ Bellman's principle
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P_0)$ be a probability space with a filtration $(\mathcal F_n)$ whose initial σ-algebra $\mathcal F_0$ is $\mathbb P_0$-trivial, fix a horizon $N$, and let $\mathcal P$ be a closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, with $\mathcal P^e\ne\emptyset$. For a value process $X$ and a stopping time $\sigma\le N$ let
--   $$
--   \Psi_\sigma(X)=\operatorname*{ess.inf}\bigl\{\mathbb E_{\mathbb Q}[X_\tau\mid\mathcal F_\sigma]\ \bigm|\ \sigma\le\tau\le N\text{ stopping time},\ \mathbb Q\in\mathcal P^e\bigr\},
--   $$
--   and let $\bar\Psi(X)$ be the generalized Snell envelope of Theorem 4.1. The following are equivalent:
--
--   1. $\mathcal P$ is stable (Definition 3.1);
--   2. for every $\mathbb Q\in\mathcal P$ and every value process $X$, $(\Psi_n(X))_{0\le n\le N}$ is a $\mathbb Q$-submartingale;
--   3. for every value process $X$, $\Psi_n(X)=\bar\Psi_n(X)$ a.s. for $0\le n\le N$;
--   4. (Bellman's principle) for every value process $X$ and all stopping times $\sigma\le\tau\le N$,
--   $$
--   \Psi_\sigma(X)=\Psi_\sigma\bigl(X^{\tau-}+\Psi_\tau({}^\tau X)\mathbf 1_{[\tau,N]}\bigr)\quad\text{a.s.}
--   $$
--
--   The theorem identifies stability under pasting as exactly the property of the set of test probabilities that makes the risk-adjusted value time consistent: the value can be computed by backward induction, and replacing the future of a position by its risk-adjusted value does not change today's value.
--
--   **Formalization Note** Two conventions the page leaves implicit are made explicit. (a) $\mathcal F_0$ is $\mathbb P_0$-trivial: the proof evaluates $\Psi_0(X)$ as the number $\inf_{\mathbb Q\in\mathcal P}\mathbb E_{\mathbb Q}[f]$, and without it the implications (1)–(3) $\Rightarrow$ stability fail (for $N=1$ and a two-atom $\mathcal F_0$, statements 2–3 hold for every $\mathcal P$ while stability can fail). (b) $\mathcal P^e\neq\emptyset$, implied by the paper's convention $\mathbb P_0\in\mathcal P$. $X_{-1}=0$. All equalities of risk-adjusted values hold $\mathbb P_0$-a.s. because essential infima are defined up to null sets.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, Theorem 4.2 (proof pp. 11–12)

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_StopOps

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Theorem 4.2: for a closed convex set of test probabilities with `𝒫ᵉ ≠ ∅` and an initial
σ-algebra `ℱ_0` that is trivial under `P₀`, stability is equivalent to each of
(i) `Ψ(X)` is a `ℚ`-submartingale for every `ℚ ∈ 𝒫` and every value process `X`;
(ii) `Ψ = Ψ̄` on value processes;
(iii) Bellman's principle `Ψ_σ(X) = Ψ_σ(X^{τ-} + Ψ_τ(^τX) 1_{[τ,N]})` for stopping times `σ ≤ τ`. -/
theorem stable_tfae {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (hℱ₀ : ∀ s, MeasurableSet[ℱ 0] s → P₀ s = 0 ∨ P₀ s = 1)
    (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) :
    List.TFAE
      [ IsStable D,
        ∀ f ∈ D.set, ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f),
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n,
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
            (hτ : IsBddStoppingTime ℱ N τ), (∀ ω, σ ω ≤ τ ω) →
            Psi D X σ hσ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) σ hσ.1 ] := by sorry

end MultiperiodRisk.Bellman
