-- Prove2me | Theorems.Thm_OnlineUBSR_sr_is_root
-- name    : OnlineUBSR.sr_is_root
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:55.184989+00:00
-- url     : https://prove2.me/theorems/ebf61550-e7ed-4aa3-85b8-761bd782def4
-- title:
--   §3, p.4 — $SR_\lambda(X)$ is finite and the unique root of $g$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $X$ a random variable with $|X|\le M_0$ a.s., $\ell:\mathbb R\to\mathbb R$ convex, $\lambda\in\mathbb R$, and $t_l<t_u$ with
--
--   $$
--   g(t_l)>0\quad\text{and}\quad g(t_u)<0\qquad(\text{Assumption 1}),
--   $$
--
--   where $g(t)=\mathbb E[\ell(-X-t)]-\lambda$. Then:
--
--   1. $t_l<SR_\lambda(X)<t_u$; in particular $SR_\lambda(X)$ is finite;
--   2. $g(SR_\lambda(X))=0$;
--   3. every $t\in[t_l,t_u]$ with $g(t)=0$ equals $SR_\lambda(X)$;
--   4. if moreover $\ell$ is nondecreasing, every $t\in\mathbb R$ with $g(t)=0$ equals $SR_\lambda(X)$.
--
--   This identifies the risk measure with the root of $g$, which is what makes stochastic root finding an estimator of $SR_\lambda(X)$.
--
--   **Formalization Note** $SR_\lambda(X)$ is the real infimum `OnlineUBSR.ubsr`; clause 1 also rules out the junk value of `sInf`.
--
--   Differences from the source:
--   - generalization: SR_λ(X) is finite → SR_λ(X) ∈ (t_l, t_u); reason: a stronger conclusion; finiteness follows
--   - generalization: convexity and monotonicity of ℓ give finiteness and uniqueness of the root → convexity alone gives clauses 1–3 (uniqueness in [t_l, t_u]); monotonicity is assumed only for clause 4 (uniqueness in ℝ); reason: the page's claim is clauses 1, 2 and 4 under both properties, which this implies
--   - encoding: λ in the interior of the range of ℓ (§2, p.3) → not assumed; reason: implied by Assumption 1 (g(t_l) > 0 > g(t_u)) and the continuity of the convex ℓ, so no instance changes
--   - encoding: the interval [t_l, t_u] of Assumption 3 and of Γ → t_l < t_u; reason: the page treats [t_l, t_u] as a nondegenerate interval; for a monotone ℓ, g(t_l) > 0 > g(t_u) forces it
--   - encoding: SR_λ(X) = inf{t ∈ ℝ : t + X ∈ A} (2) → the real sInf (OnlineUBSR.ubsr); reason: under the hypotheses the set is nonempty and bounded below (OnlineUBSR.sr_is_root), so the infimum is finite and no junk value occurs
--   - encoding: random variable; expectation → measurable X on a probability space with |X| ≤ M₀ a.s.; Bochner integral; reason: same instances; t + X ∈ A ⊂ L∞ in (2) requires a bounded X (for an unbounded X the set in (2) is empty and SR_λ(X) is not finite), which is Assumption 2; the integrand is bounded a.s.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §3, p.4 (claim after Assumption 1, citing [25, Proposition 2.3])

import Mathlib
import Definitions.Def_OnlineUBSR_gFun
import Definitions.Def_OnlineUBSR_acceptanceSet
import Definitions.Def_OnlineUBSR_ubsr

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR

/-- **Shortfall risk is finite and is the unique root of `g` (§3, p.4).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §3, p.4: "Under the above assumption, it can be shown using convexity and monotonicity of
the loss function ℓ(·) that SRλ(X) is finite, and also the unique root of the function g, i.e.,
the solution t∗ that satisfies g(t∗) = 0 coincides with SRλ(X), cf. [25, Proposition 2.3]."

For a bounded `X`, a convex loss `ℓ`, and `t_l < t_u` with `g(t_l) > 0 > g(t_u)` (Assumption 1,
Assumption 2): `SR_λ(X)` lies in `(t_l, t_u)`, `g(SR_λ(X)) = 0`, every root of `g` in `[t_l, t_u]`
equals `SR_λ(X)`, and, if `ℓ` is also nondecreasing, every root of `g` in `ℝ` equals `SR_λ(X)`.

**Formalization Note.** `SR_λ(X)` is the real `sInf` of (2) (`OnlineUBSR.ubsr`); "finite" is
rendered as membership in `(t_l, t_u)`, which also rules out the junk value of `sInf`. Convexity
alone gives the first three clauses; the page's monotonicity is the hypothesis of the fourth
(global uniqueness). The page writes `[t_l, t_u]`, so `t_l < t_u` is assumed. The position of `λ`
in the interior of the range of `ℓ` (§2) is not assumed: it follows from Assumption 1. -/
theorem sr_is_root
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (M₀ : ℝ) (hA2 : ∀ᵐ ω ∂μ, |X ω| ≤ M₀)
    (ℓ : ℝ → ℝ) (hℓconv : ConvexOn ℝ Set.univ ℓ)
    (lam tl tu : ℝ) (htlu : tl < tu)
    (hA1l : 0 < gFun μ ℓ lam X tl) (hA1u : gFun μ ℓ lam X tu < 0) :
    ubsr μ ℓ lam X ∈ Set.Ioo tl tu ∧
    gFun μ ℓ lam X (ubsr μ ℓ lam X) = 0 ∧
    (∀ t ∈ Set.Icc tl tu, gFun μ ℓ lam X t = 0 → t = ubsr μ ℓ lam X) ∧
    (Monotone ℓ → ∀ t : ℝ, gFun μ ℓ lam X t = 0 → t = ubsr μ ℓ lam X) := by sorry

end OnlineUBSR
