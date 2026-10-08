-- Prove2me | Theorems.Thm_NetworkControl_UtilityFairness_theorem_lyapunov_optimization_v2
-- name    : NetworkControl.UtilityFairness.theorem_lyapunov_optimization_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:23.210476+00:00
-- url     : https://prove2.me/theorems/434987a6-8b1a-4271-b9dc-89abcda9dc51
-- title:
--   Theorem 5.4 — Lyapunov optimization (corrected: $\bar g$ and the limsup in the extended reals)
-- statement:
--   Let $U(t)\in\mathbb R^N_{\ge 0}$ be a backlog process, $R(t)\in\mathbb R^K$ a rate process, $g:\mathbb R^K\to\mathbb R$ a concave utility, $g^*$ a target value, $L\ge 0$ a Lyapunov function with $\mathbb E\,L(U(t))<\infty$, and $\Delta(U(t))$ the one-step drift. Suppose there are constants $V,\varepsilon,B>0$ such that for every slot $t$
--   $$\Delta(U(t))-V\,\mathbb E\{g(R(t))\mid U(t)\}\le B-\varepsilon\sum_{i=1}^N U_i(t)-Vg^*\qquad\text{a.s.}\tag{5.19}$$
--   Define $r(t):=\frac1t\sum_{\tau<t}\mathbb E\,R(\tau)$ (5.18) and $\bar g:=\limsup_{t\to\infty}\frac1t\sum_{\tau<t}\mathbb E\,g(R(\tau))\in(-\infty,+\infty]$. Then
--   $$\varepsilon\cdot\limsup_{t\to\infty}\frac1t\sum_{\tau<t}\sum_{i}\mathbb E\,U_i(\tau)\le B+V(\bar g-g^*)\tag{5.20}$$
--   and
--   $$\liminf_{t\to\infty}g(r(t))\ge g^*-\frac BV.\tag{5.21}$$
--
--   **Formalization Note.** The retired statement computed $\bar g$ with `Filter.limsup` on $\mathbb R$, which is the junk value $0$ when the averages of $\mathbb E\,g(R(\tau))$ are unbounded above — (5.19) bounds them only from below — so the right-hand side of (5.20) became negative (the accepted disproof). The corrected statement reads $\bar g$ and both asymptotic quantities in `EReal`, as the monograph's extended-real convention intends; (5.20) is written in the multiplied-out form $\varepsilon\cdot\limsup\le B+V(\bar g-g^*)$ to avoid division in `EReal` (equivalent since $\varepsilon>0$). Under (5.19) the averages of $\mathbb E\,g(R(\tau))$ are bounded below, so $\bar g>-\infty$ and the right-hand side is never $-\infty$. Nonnegativity of backlogs is the monograph's standing assumption and is stated explicitly.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Foundations and Trends in Networking 1(1), 2006, p. 82, Theorem 5.4 (Lyapunov Optimization), with (5.18)-(5.21)

import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift

namespace NetworkControl.UtilityFairness

open MeasureTheory

/-- Theorem 5.4 (Lyapunov Optimization), Georgiadis–Neely–Tassiulas p. 82. Let `L ≥ 0` with
`E L(U(0)) < ∞`, let `g` be a concave utility of the `K`-dimensional rate vector, and let
`V, ε, B > 0` be such that for every slot `t`
`∆(U(t)) - V·E{g(R(t)) | U(t)} ≤ B - ε Σ_i U_i(t) - V·g*` (5.19). Then, with
`r(t) := (1/t) Σ_{τ<t} E R(τ)` (5.18) and `ḡ := limsup_t (1/t) Σ_{τ<t} E g(R(τ))`,
`limsup_t (1/t) Σ_{τ<t} Σ_i E U_i(τ) ≤ (B + V(ḡ - g*))/ε` (5.20) and
`liminf_t g(r(t)) ≥ g* - B/V` (5.21).

Corrected version: `ḡ` and the two `limsup`/`liminf` are read in the extended reals `EReal`
(the monograph's `+∞` is not representable in `ℝ`, where `Filter.limsup` of an unbounded sequence
is the junk value `0`); (5.20) is written in the equivalent multiplied-out form
`ε · limsup ≤ B + V(ḡ - g*)` to avoid division in `EReal`. Backlogs are nonnegative, as
throughout the monograph. -/
theorem theorem_lyapunov_optimization_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N K : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (R : ℕ → Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ) (gstar : ℝ)
    (hgConcave : ConcaveOn ℝ Set.univ g)
    (V ε B : ℝ) (hV : 0 < V) (hε : 0 < ε) (hB : 0 < B)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL : ∀ t : ℕ, Integrable (fun ω => L (U t ω)) P)
    (hIntegG : ∀ t : ℕ, Integrable (fun ω => g (R t ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin N, Integrable (fun ω => U t ω i) P)
    (hIntegR : ∀ t : ℕ, ∀ k : Fin K, Integrable (fun ω => R t ω k) P)
    (hdrift : ∀ t : ℕ,
      ((fun ω => drift P L U t ω
          - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω))
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin N, U t ω i - V * gstar)) :
    ((ε : EReal) *
        Filter.limsup
          (fun t : ℕ =>
            (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
          Filter.atTop
      ≤ (B : EReal) + (V : EReal) *
          (Filter.limsup
            (fun t : ℕ => (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P : ℝ) : EReal))
            Filter.atTop - (gstar : EReal))) ∧
    (((gstar - B / V : ℝ) : EReal) ≤
      Filter.liminf
        (fun t : ℕ =>
          ((g (fun k : Fin K => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω k ∂P) : ℝ) : EReal))
        Filter.atTop) := by sorry

end NetworkControl.UtilityFairness
