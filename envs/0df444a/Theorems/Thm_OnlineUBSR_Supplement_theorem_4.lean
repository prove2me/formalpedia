-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_theorem_4
-- name    : OnlineUBSR.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:41:42.966872+00:00
-- url     : https://prove2.me/theorems/24ace373-d7b8-4733-aad7-66d546dd5292
-- title:
--   Theorem 4 (corrected: base assumptions and Lipschitz premise) — high-probability $c/k^\alpha$ bound
-- statement:
--   Under Assumptions 1–4 (with the three corrections of Theorem 1) and $|\ell'|\le L_1$ on $[-M_0-t_u,M_0-t_l]$ (the Lipschitz property the proof uses), set $a_k=c/k^\alpha$ with $0<\alpha<1$, choose $n_0$ with $L_1^2a_{n_0}<\mu_1$, and let $\delta\in(0,1)$. For every $n\ge n_0$, the event
--   $$|t_n-SR_\lambda(X)|\le C_2e^{-\mu_1cn^{1-\alpha}/(2(1-\alpha))}+\frac{C_3}{n^{\alpha/2}}$$
--   has probability at least $1-\delta$, with $C_2,C_3$ exactly as printed in (8).
--
--   Differences from the source:
--   - correction: Assumption 3 bounds $-\ell'(-t)$ → Lean bounds $g'(t)$; reason: the proof uses $g'$ and the printed condition is false for nonzero $X$
--   - correction: Assumption 4 starts at $n\ge1$ → Lean includes $n=0$; reason: the first recursion step uses it
--   - correction: the source leaves $t_0$ unrestricted → Lean requires $t_0\in[t_l,t_u]$; reason: the proof uses interval control at the initial point
--   - correction: the theorem assumes only Assumptions 1–4 → Lean adds $|\ell'(x)|\le L_1$ on $[-M_0-t_u,M_0-t_l]$, the range of $\xi-t$; reason: the proof uses "$\ell$ is $L_1$ Lipschitz" (pp.20, 24), and without it the bound is false: $\xi\in\{0,1\}$ with $P(\xi=1)=p$, $\ell(x)=x+\psi(x)/p$ ($\psi$ the convex $C^1$ Huber function) satisfies Assumptions 1–4 with $\mu_1=1,L_1=2,M_0=1$, yet one rare sample at step $n$ moves $t_n$ far past the right side with probability about $p>\delta=p/2$ (DISPROOF.md)
--   - encoding: a bound holds with probability at least $1-\delta$ → the measure of the displayed event is at least $\operatorname{ofReal}(1-\delta)$; reason: this is the direct measure-theoretic encoding
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 4, p.7, equation (8)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR.Supplement

/-- **Theorem 4 (high-probability error bound for `c/k^α`).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 4, p.7, (8).

**Formalization Note.** The statement keeps the printed constants `C₂,C₃`, including the
factor printed in `C₂`; no factor suggested only by the proof is inserted. The event has
probability at least `1-δ`. Assumptions 3 and 4 and the initial point use the three corrections
of the published Theorem 1.

**Source correction (Lipschitz premise).** The concentration step of the proofs of Theorems 2 and 4
uses "the fact that `ℓ` is `L₁` Lipschitz" (p.20; Theorem 4's proof applies the resulting (35)), which neither printed nor corrected Assumption 3
supplies. Without it the printed bound is false: with `ξ ∈ {0, 1}` (`P(ξ=1)=p`),
`ℓ(x)=x+ψ(x)/p` for the convex `C¹` Huber function `ψ`, Assumptions 1--4 hold with
`μ₁=1, L₁=2, M₀=1`, but a single rare sample at step `n` moves `tₙ` by about `1/(8pn)` (resp.
`1/(8p√n)`), far beyond the right side, with probability `≈ p > δ = p/2` (DISPROOF.md). The
hypothesis `hLip` bounds `|ℓ'|` by `L₁` on `[-M₀-tu, M₀-tl]`, the range of `ξ-t`, which is
the minimal form of the paper's Lipschitz fact. -/
theorem theorem_4
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (ξ : ℕ → Ω → ℝ) (hξ : ∀ n, Measurable (ξ (n + 1)))
    (hind : iIndepFun (fun n => ξ (n + 1)) μ)
    (hident : ∀ n, IdentDistrib (ξ (n + 1)) (fun ω => -X ω) μ μ)
    (ℓ : ℝ → ℝ) (hℓconv : ConvexOn ℝ Set.univ ℓ) (hℓdiff : Differentiable ℝ ℓ)
    (lam tl tu : ℝ) (htlu : tl < tu)
    (hA1l : 0 < OnlineUBSR.gFun μ ℓ lam X tl)
    (hA1u : OnlineUBSR.gFun μ ℓ lam X tu < 0)
    (M₀ : ℝ) (hA2 : ∀ᵐ ω ∂μ, |X ω| ≤ M₀)
    (μ₁ L₁ : ℝ) (hμ₁ : 0 < μ₁) (hL₁ : 0 < L₁)
    (hA3 : ∀ t ∈ Set.Icc tl tu,
      -L₁ ≤ deriv (OnlineUBSR.gFun μ ℓ lam X) t ∧
        deriv (OnlineUBSR.gFun μ ℓ lam X) t ≤ -μ₁)
    (hLip : ∀ x ∈ Set.Icc (-M₀ - tu) (M₀ - tl), |deriv ℓ x| ≤ L₁)
    (σ : ℝ) (hσ : 0 < σ) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc tl tu)
    (c : ℝ) (hc : 0 < c) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hcut : c / (n₀ : ℝ) ^ α * L₁ ^ 2 < μ₁)
    (hA4 : EstimationNoiseBound μ ℓ lam tl tu t₀ σ X
      (fun k : ℕ => c / (k : ℝ) ^ α) ξ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) (hn : n₀ ≤ n) :
    let Ctilde := (1 + c * L₁) ^ (2 * n₀) *
      Real.exp (μ₁ * c * (n₀ : ℝ) ^ (1 - α) / (1 - α))
    let C₂ := 8 * L₁ * M₀ *
          Real.sqrt (Real.log (1 / δ) * (1 + c ^ 2 * L₁ ^ 2) ^ (n₀ + 1) * c ^ 2 /
            (c ^ 2 * L₁ ^ 2)) +
        Real.sqrt (Ctilde * ((t₀ - OnlineUBSR.ubsr μ ℓ lam X) ^ 2 + σ ^ 2 * c ^ 2 * n₀))
    let C₃ := 8 * L₁ * M₀ *
          Real.sqrt (Real.log (1 / δ) * 2 * (μ₁ * c) ^ (α / (1 - α)) * c ^ 2 /
            (1 - α)) +
        Real.sqrt (σ ^ 2 * 2 * (2 * μ₁ * c) ^ (α / (1 - α)) * c ^ 2 / (1 - α))
    ENNReal.ofReal (1 - δ) ≤ μ {ω |
      |OnlineUBSR.iterate ℓ lam tl tu t₀ (fun k : ℕ => c / (k : ℝ) ^ α) ξ n ω -
          OnlineUBSR.ubsr μ ℓ lam X| ≤
        C₂ * Real.exp (-(μ₁ * c * (n : ℝ) ^ (1 - α) / (2 * (1 - α)))) +
          C₃ / (n : ℝ) ^ (α / 2)} := by sorry

end OnlineUBSR.Supplement
