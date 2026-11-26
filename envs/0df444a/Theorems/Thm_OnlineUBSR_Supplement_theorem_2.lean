-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_theorem_2
-- name    : OnlineUBSR.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:36:10.101057+00:00
-- url     : https://prove2.me/theorems/8d7d3fd7-9110-5a6b-ae04-ccbee3600be0
-- title:
--   Theorem 2 (corrected: base assumptions, Lipschitz premise, initial-error reading) — high-probability $c/k$ bound
-- statement:
--   Under Assumptions 1–4, with the corrected derivative condition, corrected noise indexing, and $t_0\in[t_l,t_u]$, and with $|\ell'|\le L_1$ on $[-M_0-t_u,M_0-t_l]$ (the Lipschitz property the proof uses), set $a_k=c/k$ and assume $\mu_1c>1/2$. For every $n\ge1$ and $\delta\in(0,1)$, the event
--   $$
--   |t_n-SR_\lambda(X)|\le \sqrt{\frac{\log(1/\delta)}{C_1n}}+e^{L_1^2c^2\pi^2/12}\left[\frac{|t_0-SR_\lambda(X)|}{n^{\mu_1c}}+\frac{c\sigma2^{2\mu_1c}}{\sqrt{2\mu_1c-1}\sqrt n}\right]
--   $$
--   has probability at least $1-\delta$, where $C_1$ is the constant printed in (7).
--
--   This is the paper's concentration companion to the published mean-squared error theorem.
--
--   Differences from the source:
--   - correction: Assumption 3 bounds $-\ell'(-t)$ → Lean bounds $g'(t)$ on $[t_l,t_u]$; reason: the proof uses $g'$ and the printed condition is false for nonzero $X$
--   - correction: Assumption 4 starts at $n\ge1$ → Lean includes $n=0$; reason: the first recursion step uses the index-zero noise bound
--   - correction: the source leaves $t_0$ unrestricted → Lean requires $t_0\in[t_l,t_u]$; reason: the proof applies the interval derivative bound at $t_0$
--   - correction: the theorem assumes only Assumptions 1–4 → Lean adds $|\ell'(x)|\le L_1$ on $[-M_0-t_u,M_0-t_l]$, the range of $\xi-t$; reason: the proof uses "$\ell$ is $L_1$ Lipschitz" (p.20), and without it the bound is false: $\xi\in\{0,1\}$ with $P(\xi=1)=p$, $\ell(x)=x+\psi(x)/p$ ($\psi$ the convex $C^1$ Huber function) satisfies Assumptions 1–4 with $\mu_1=1,L_1=2,M_0=1$, yet one rare sample at step $n$ moves $t_n$ far past the right side with probability about $p>\delta=p/2$ (DISPROOF.md)
--   - reading: $\mathbb E|t_1-t^*|$ → $|t_0-SR_\lambda(X)|$; reason: Remark 1 calls the initial point $t_1$ while (5), Theorem 1, and the proof use $t_0$
--   - encoding: a bound holds with probability at least $1-\delta$ → the measure of the displayed event is at least $\operatorname{ofReal}(1-\delta)$; reason: this is the direct measure-theoretic encoding
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 2, p.6, equation (7)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR.Supplement

/-- **Theorem 2 (high-probability error bound for `c/k`).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 2, p.6, (7).

**Formalization Note.** The three corrections already required by the published Theorem 1 are
repeated here: Assumption 3 bounds `g'`; Assumption 4 includes index zero; and `t₀` lies in the
projection interval. The printed `E|t₁-t*|` is read as the deterministic initial error
`|t₀-SR_λ(X)|`, as fixed by Remark 1 and the proof on p.21. Probability is the measure of the
displayed event, and all noninteger powers are real powers.

**Source correction (Lipschitz premise).** The concentration step of the proofs of Theorems 2 and 4
uses "the fact that `ℓ` is `L₁` Lipschitz" (p.20; Theorem 4's proof applies the resulting (35)), which neither printed nor corrected Assumption 3
supplies. Without it the printed bound is false: with `ξ ∈ {0, 1}` (`P(ξ=1)=p`),
`ℓ(x)=x+ψ(x)/p` for the convex `C¹` Huber function `ψ`, Assumptions 1--4 hold with
`μ₁=1, L₁=2, M₀=1`, but a single rare sample at step `n` moves `tₙ` by about `1/(8pn)` (resp.
`1/(8p√n)`), far beyond the right side, with probability `≈ p > δ = p/2` (DISPROOF.md). The
hypothesis `hLip` bounds `|ℓ'|` by `L₁` on `[-M₀-tu, M₀-tl]`, the range of `ξ-t`, which is
the minimal form of the paper's Lipschitz fact. -/
theorem theorem_2
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
    (c : ℝ) (hc : 1 / 2 < μ₁ * c)
    (hA4 : EstimationNoiseBound μ ℓ lam tl tu t₀ σ X (fun k : ℕ => c / (k : ℝ)) ξ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) (hn : 1 ≤ n) :
    let C₁ := (2 * μ₁ * c - 1) /
        ((2 : ℝ) ^ (4 * μ₁ * c + 4) * c ^ 2 * L₁ ^ 2 * M₀ ^ 2) *
          Real.exp (-(L₁ ^ 2 * c ^ 2 * Real.pi ^ 2 / 6))
    ENNReal.ofReal (1 - δ) ≤ μ {ω |
      |OnlineUBSR.iterate ℓ lam tl tu t₀ (fun k : ℕ => c / (k : ℝ)) ξ n ω -
          OnlineUBSR.ubsr μ ℓ lam X| ≤
        Real.sqrt (Real.log (1 / δ) / (C₁ * n)) +
          Real.exp (L₁ ^ 2 * c ^ 2 * Real.pi ^ 2 / 12) *
            (|t₀ - OnlineUBSR.ubsr μ ℓ lam X| / (n : ℝ) ^ (μ₁ * c) +
              c * σ * (2 : ℝ) ^ (2 * μ₁ * c) /
                (Real.sqrt (2 * μ₁ * c - 1) * Real.sqrt n))} := by sorry

end OnlineUBSR.Supplement
