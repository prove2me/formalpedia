-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_proposition_4_4
-- name    : JuHardCoreTransition.Mixing.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:30.292809+00:00
-- url     : https://prove2.me/theorems/7995c8a0-cfb0-46cd-87df-2aab7d386a1b
-- title:
--   Proposition 4.4 — integrated spectral-stability bound
-- statement:
--   There are absolute constants $K\ge2$ and $C>0$ with the following property. Let $G$ have $n\ge1$ vertices and maximum degree at most $d\ge3$. For every $0<\lambda\le(1+\delta_{\mathrm{up}})\lambda_c$, the law $\mu_{G,\lambda}$ satisfies field-dynamics spectral stability with the nondecreasing rate $\mathcal C\ge1$ defined by
--   $$\mathcal C(a)=\begin{cases}\min\{K(1+\sqrt{n/d}),[1-(d-1)\theta_d(a)]^{-1}\},&0<a<\lambda_c,\\ K\big(1+\sqrt{n/d}+(n/d)(a/\lambda_c-1)\big),&\lambda_c\le a\le(1+\delta_{\mathrm{up}})\lambda_c.\end{cases}$$
--   Moreover its stability integral $I(\lambda)=\int_0^\lambda\frac{\mathcal C(a)-1}a\,da$ is finite and satisfies
--   $$I(\lambda)\le\begin{cases}2\big(1+\frac1{d-2}\big)[\log\mathcal C(\lambda)+1],&\lambda<\lambda_c,\\ \big(1+\frac1{d-2}\big)\log(1+n/d)+\frac{Cn\delta^2}d+C,&\lambda\ge\lambda_c,\end{cases}$$
--   where $\delta=\lambda/\lambda_c-1$ in the second case.
--
--   Differences from the source:
--   - encoding: an n-vertex graph G=(V,E) → a SimpleGraph on Fin n (n labelled vertices); reason: every finite graph is isomorphic to one on Fin n and every quantity involved is isomorphism-invariant; this lets the absolute constant be stated before the graph
--   - encoding: the nondecreasing rate C ≥ 1 defined by (4.5) → rateProp44 K n d, with MonotoneOn on (0, λ] and C ≥ 1 there as conclusions; reason: the properties claimed of the rate are stated
--   - encoding: I(λ) = ∫_0^λ (C(a) − 1)/a da is finite → stabIntegral (Lebesgue integral over (0, λ] in [0, ∞]) ≠ ⊤, and the bounds on its real value; reason: for a nonnegative integrand the improper integral is the Lebesgue integral
--   - encoding: δ = λ/λ_c − 1 in the second case → δ written out as lam / lamCrit d − 1; reason: substitution
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Proposition 4.4, printed p.19 / PDF p.20

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Proposition 4.4 (Integrated spectral-stability bound)** (printed p.19 / PDF p.20). There
are absolute constants `K ≥ 2` and `C > 0` such that for every graph `G` on `n ≥ 1` vertices of
maximum degree at most `d ≥ 3` and every `0 < λ ≤ (1 + δ_up)λ_c`, `μ_{G,λ}` satisfies
field-dynamics spectral stability with the rate `C(a)` of (4.5) (`rateProp44 K n d`), which is
nondecreasing and at least one on `(0, λ]`; its stability integral `I(λ) = ∫_0^λ (C(a) − 1)/a da`
is finite and satisfies (4.6): `I(λ) ≤ 2(1 + 1/(d−2))[log C(λ) + 1]` for `λ < λ_c`, and
`I(λ) ≤ (1 + 1/(d−2)) log(1 + n/d) + Cnδ²/d + C` for `λ ≥ λ_c`, with `δ = λ/λ_c − 1`.
(The vertex set of an `n`-vertex graph is `Fin n`.) -/
theorem proposition_4_4 :
    ∃ K C : ℝ, 2 ≤ K ∧ 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ n : ℕ, 1 ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ v, G.degree v ≤ d) →
      ∀ lam : ℝ, 0 < lam → lam ≤ (1 + deltaUp) * lamCrit d →
        IsStabilityRate G lam (rateProp44 K n d) ∧
        MonotoneOn (rateProp44 K n d) (Set.Ioc 0 lam) ∧
        (∀ a ∈ Set.Ioc (0 : ℝ) lam, 1 ≤ rateProp44 K n d a) ∧
        stabIntegral (rateProp44 K n d) lam ≠ ⊤ ∧
        (lam < lamCrit d →
          (stabIntegral (rateProp44 K n d) lam).toReal ≤
            2 * (1 + 1 / ((d : ℝ) - 2)) * (Real.log (rateProp44 K n d lam) + 1)) ∧
        (lamCrit d ≤ lam →
          (stabIntegral (rateProp44 K n d) lam).toReal ≤
            (1 + 1 / ((d : ℝ) - 2)) * Real.log (1 + (n : ℝ) / d) +
              C * (n : ℝ) * (lam / lamCrit d - 1) ^ 2 / d + C) := by sorry

end JuHardCoreTransition.Mixing
