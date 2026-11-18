-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_7
-- name    : IAFTRL.lemma_G_7
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T15:58:30.599024+00:00
-- url     : https://prove2.me/theorems/3ad87f8c-e1aa-48c7-932d-93d4eef71c44
-- title:
--   Lemma G.7 — the comparison law built from a centered allocation is feasible in program (3.6)
-- statement:
--   **Setting.** Fix a round $n\ge1$ of GIA-FTRL (Algorithm 2) with cumulative estimate $S$. The objects are:
--   - $\mathcal K=\mathrm{Conv}\,\mathcal B$, a compact generator $\mathcal B$, and $\Delta(a)=(a-a^*)^\top\theta$ with $0\le\Delta\le2$ on $\mathcal K$ and $a^*\in\mathcal K$;
--   - the exponential-weights law $q_n\propto e^{-x^\top S/\beta_n}\mu(dx)$ and $\pi^*=\mu\{a^*\}>0$;
--   - a finite feasible centered sampling allocation $n_{\rm des}$ on $\mathcal B$ (1.4), with total mass $N$.
--
--   For $L\ge1$ put $\rho=16BL^2/n$ and define the comparison law (Definition G.2)
--   $$p^c=(1-\gamma)\,q_n+\rho\,n_{\rm des}|_{\{a\ne a^*\}},\qquad\gamma=\rho\,n_{\rm des}(\{a\ne a^*\}).$$
--
--   **Claim.** Assume the following, which are the properties of the comparison event $W_t$ used in the source:
--   1. the reference action of (3.4) is $a^*$;
--   2. $X(a)=(a-a^*)^\top S\ge0$ on $\mathcal K$;
--   3. $\Delta(a)\le L\,X(a)/n$ on $\mathcal K$;
--   4. $\rho\le1$ and $\rho N\le\min\{\Gamma_n,1/4\}$;
--   5. $q_n(a^*)\ge3/4$;
--   6. $64\int_{a\ne a^*}e^{-X/(2\beta_n)}d\mu\le2d\rho^2\pi^*$.
--
--   Then $p^c$ is feasible in program (3.6) at round $n$: the mixture budget, positive-definite design, update-magnitude, second-moment and proxy constraints all hold.
--
--   **Formalization Note.** This is Lemma G.7 in explicit-hypothesis form: the event $W_t$ is replaced by the consequences of its definition and of Lemma G.3 that the proof uses.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.4.1, Definition G.2 and Lemma G.7, (G.114)–(G.140)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.7 (The comparison distribution constructed from a centered sampling allocation
satisfies all budgets).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.7, pp.134–137: "For `t ≥ T*`, on `W_t`, the
distribution `p^c_t = (1 − γ^c_t) q_t + ρ_t n|_{A∖{a*}}` with mark `v(x) = Σ(p^c_t)^{−1} x` is
feasible in (3.6)", with `ρ_t = 16 B L_t² / t` (Definition G.2).

Explicit-hypothesis form: the properties of the event `W_t` used in the proof are assumed
directly — the reference is `a*`, `X_t ≥ 0` on `𝒦`, the ratio bound `Δ ≤ L X_t/t`, the two
feasibility thresholds in the form `ρ ≤ 1`, `ρ N_n ≤ min(Γ_t, 1/4)`, the atom mass
`q_t(a*) ≥ 3/4`, and the proxy budget `64 ∫_{a≠a*} e^{−X_t/(2β_t)} dµ ≤ 2d ρ² µ(a*)` supplied by
Lemma G.3. -/
theorem lemma_G_7 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (θ astar : Fin d → ℝ) (haK : astar ∈ Kset ℬ)
    (hΔ0 : ∀ a ∈ Kset ℬ, 0 ≤ (a - astar) ⬝ᵥ θ) (hΔ2 : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ θ ≤ 2)
    (ν : Measure (Fin d → ℝ)) (hν : IsCtrAlloc ℬ θ astar ν)
    (n : ℕ) (hn : 1 ≤ n) (S : Fin d → ℝ) (href : gref ℬ e n S = astar)
    (hX0 : ∀ a ∈ Kset ℬ, 0 ≤ (a - astar) ⬝ᵥ S) (L : ℝ) (hL : 1 ≤ L)
    (hgapL : ∀ a ∈ Kset ℬ, (a - astar) ⬝ᵥ θ ≤ L * ((a - astar) ⬝ᵥ S / n))
    (hρ1 : 16 * gB d * L ^ 2 / n ≤ 1)
    (hN : 16 * gB d * L ^ 2 / n * (ν Set.univ).toReal ≤ gGam d n)
    (hN4 : 16 * gB d * L ^ 2 / n * (ν Set.univ).toReal ≤ 1 / 4)
    (hq : 3 / 4 ≤ (gq ℬ e n S {astar}).toReal)
    (ha : 0 < refMu ℬ e {astar})
    (hprox : 64 * ∫ x in {astar}ᶜ, Real.exp (-((x - astar) ⬝ᵥ S) / (2 * gbeta d n))
        ∂(refMu ℬ e) ≤ 2 * d * (16 * gB d * L ^ 2 / n) ^ 2 * (refMu ℬ e {astar}).toReal) :
    IsFeasible3_6 ℬ e n S
      (ENNReal.ofReal (1 - ((ENNReal.ofReal (16 * gB d * L ^ 2 / n) •
          ν.restrict {astar}ᶜ) Set.univ).toReal) • gq ℬ e n S +
        ENNReal.ofReal (16 * gB d * L ^ 2 / n) • ν.restrict {astar}ᶜ) := by sorry

end IAFTRL
