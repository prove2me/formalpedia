-- Prove2me | Theorems.Thm_GradedReserve_Supplement_theorem_3_6
-- name    : GradedReserve.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:52:23.400439+00:00
-- url     : https://prove2.me/theorems/b3a9ff8c-24a6-471c-a264-7f4a7b181ccd
-- title:
--   Theorem 3.6 — hard reserves are not optimal; the Lipschitz condition is needed
-- statement:
--   Assume the standing assumptions of Section 3: $n\ge2$, values i.i.d. on $[0,1]$ with a density $f$ positive on $(0,1)$, $F$ regular, $\varepsilon\in(0,1)$, $\tau=(1-\varepsilon)R^*$ and $R_n(0)<\tau$. Let $r=r^-_\varepsilon$ satisfy $0<r<r^*$, and let $f$ and $\varphi$ be Lipschitz on a neighbourhood of $r$. For $h>0$, $\rho\in[0,1]$ and $r'$, accept the highest bid with probability $0$ below $r-h$, $\rho$ on $[r-h,r')$ and $1$ on $[r',1]$, with $r'=r'(\rho)$ chosen so that the rational revenue equals $\tau$ and $r'(0)=r$. Then:
--
--   1. there is $h_0>0$ such that for every $h\in(0,h_0)$ such a revenue-preserving curve continuous at $\rho=0$ exists, and along every such curve the right derivative at $\rho=0$ of the anchored revenue is
--   $$\Gamma(h)=n\int_{r-h}^r vQf\,dv+nrQ(r)f(r)\frac{\int_{r-h}^rQ}{Q(r)}-\frac r{\varphi(r)}\,n\int_{r-h}^r\varphi Qf;$$
--   2. $\Gamma(h)=nrQ(r)f(r)\,h+O(h^2)$ as $h\downarrow0$, and $\Gamma(h)>0$ for all small $h>0$;
--   3. the first-price auction with reserve $r^-_\varepsilon$ is not optimal in $G$: some $\tau$-admissible graded reserve has strictly larger anchored revenue than $\mathbf 1\{b\ge r^-_\varepsilon\}$.
--
--   The Lipschitz condition is needed: for $n=2$ and the density $f=\tfrac12$ on $[0,0.3)$, $\tfrac{17}{14}$ on $(0.3,1]$, which is a regular value density, there is $\varepsilon\in(0,1)$ with $r^-_\varepsilon=0.3$ (and $R_2(0)<\tau$, $0.3<r^*$), and for small $h$ the right derivative $\Gamma(h)$ of the anchored revenue along every revenue-preserving curve continuous at $0$ exists and satisfies
--   $$\lim_{h\downarrow0}\frac{\Gamma(h)}h=-\frac9{2800}.$$
--
--   The theorem shows that a band of low acceptance probability just below the lowest admissible hard reserve raises anchored revenue at no cost to the rational guarantee.
--
--   **Formalization Note** The derivative is a right derivative in $\rho$ at $0$; $O(h^2)$ is `Asymptotics.IsBigO` along $h\downarrow0$.
--
--   Differences from the source:
--   - encoding: Section 3 standing assumption: F regular and R_n(0) < τ < R*, density positive on (0,1), n ≥ 2 → hypotheses IsValueDensity f, IsRegular f, 2 ≤ n, ε ∈ (0,1), R_n(0) < (1 − ε)R*; reason: §3.4 lies in Section 3; τ < R* follows from ε > 0 and R* > 0
--   - encoding: f and φ Lipschitz near r → LipschitzOnWith on some neighbourhood U ∈ 𝓝 r, for f and for φ; reason: the meaning of "near"
--   - encoding: φQf in Γ(h) → (v f(v) − (1 − F(v))) Q(v); reason: equal wherever f > 0; avoids x/0 = 0
--   - reading: with r′ chosen so that the rational revenue equals τ; the derivative of the anchored revenue in ρ at ρ = 0 is Γ(h) → ∃ h₀ > 0 such that for h ∈ (0,h₀) a revenue-preserving curve r′ (IsRevPreserving: r′(0) = r, a symmetric BNE exists and every symmetric BNE has rational revenue τ on [0,δ)) continuous at 0 exists, and along every such curve the right derivative at ρ = 0 of revAnc is Γ(h); reason: ρ is a probability, so the derivative is one-sided; the curve is locally unique (R′_n(r) > 0), so the derivative along every such curve is the stated one; "for small h"
--   - encoding: Γ(h) = nrQ(r)f(r)h + O(h²) → (Γ(h) − nrQ(r)f(r)h) =O[𝓝[>] 0] h²; reason: the meaning of O as h ↓ 0
--   - encoding: > 0 for small h → ∀ᶠ h in 𝓝[>] 0, 0 < Γ(h); reason: the meaning of "for small h"
--   - reading: the first-price auction with reserve r⁻_ε is not optimal in G → some τ-admissible graded reserve π has revAnc π > revAnc 1{b ≥ r⁻_ε}; reason: the definition of optimality in G (display (2))
--   - encoding: the density 1/2 on [0,0.3) and 17/14 on (0.3,1] (value at 0.3 unspecified) → exampleDensity with value 17/14 at 0.3 and 0 outside [0,1]; reason: one point changes no law and no revenue; with 17/14 the virtual value is strictly increasing on (0,1)
--   - reading: for the regular density …, two bidders and the ε for which r⁻_ε = 0.3, the same perturbation has lim Γ(h)/h = −9/2800 → conclusions: the density is a value density and regular; ∃ ε ∈ (0,1) with r⁻_ε = 0.3, R_2(0) < τ and 0.3 < r*; ∃ h₀, Γ such that for h ∈ (0,h₀) a revenue-preserving curve exists and every one continuous at 0 gives right derivative Γ(h); Γ(h)/h → −9/2800 as h ↓ 0; reason: "regular" and the existence of ε are claims of the text, stated rather than assumed; Γ(h) is the derivative, since the closed formula uses f(r), φ(r), which jump at 0.3
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.6, p.8 (PDF 9); proof Section A.4, pp.16–17 (PDF 17–18)

import Mathlib
import Definitions.Def_GradedReserve_IsValueDensity
import Definitions.Def_GradedReserve_IsRegular
import Definitions.Def_GradedReserve_IsGradedReserve
import Definitions.Def_GradedReserve_IsTauAdmissible
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_valueCdf
import Definitions.Def_GradedReserve_virtualValue
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_optRevenue
import Definitions.Def_GradedReserve_rStar
import Definitions.Def_GradedReserve_revAnc
import Definitions.Def_GradedReserve_Supplement_rMinus
import Definitions.Def_GradedReserve_Supplement_twoTier
import Definitions.Def_GradedReserve_Supplement_gammaH
import Definitions.Def_GradedReserve_Supplement_IsRevPreserving
import Definitions.Def_GradedReserve_Supplement_exampleDensity
open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

namespace GradedReserve.Supplement

/-- **Theorem 3.6** (Hard reserves are not optimal) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.6, p.8, PDF 9; proof Section
A.4, pp.16–17, PDF 17–18). Assume Section 3's standing assumptions: `n ≥ 2`, a value density `f`
positive on `(0, 1)`, `F` regular, `ε ∈ (0, 1)`, `τ = (1 − ε)R*` and `R_n(0) < τ`. Let
`0 < r⁻_ε < r*` and let `f` and `φ` be Lipschitz near `r = r⁻_ε`. Accept the highest bid with
probability `0` below `r − h`, with probability `ρ` on `[r − h, r′)`, and with probability one on
`[r′, 1]`, with `r′` chosen so that the rational revenue equals `τ`. Then for every small `h > 0`
a revenue-preserving choice `ρ ↦ r′(ρ)` with `r′(0) = r` exists, and along every such choice that
is continuous at `ρ = 0` the right derivative of the anchored revenue in `ρ` at `ρ = 0` is
$$\Gamma(h)=n\int_{r-h}^r vQf\,dv+nrQ(r)f(r)\frac{\int_{r-h}^rQ}{Q(r)}-\frac{r}{\varphi(r)}\,n\int_{r-h}^r\varphi Qf
=nrQ(r)f(r)\,h+O(h^2)>0$$
for small `h`, so the first-price auction with reserve `r⁻_ε` is not optimal in `G`. For the
regular density `1/2` on `[0, 0.3)` and `17/14` on `(0.3, 1]`, two bidders and the `ε` for which
`r⁻_ε = 0.3`, the same perturbation has the one-sided limit `lim_{h↓0} Γ(h)/h = −9/2800`.

**Formalization Note.** "Lipschitz near `r`" is Lipschitz continuity of `f` and of `φ` on a
neighbourhood of `r`. The `O(h²)` is `Asymptotics.IsBigO` as `h ↓ 0` (an existential constant).
"Not optimal in `G`" is: some `τ`-admissible graded reserve has strictly larger anchored revenue
than the hard reserve `1{b ≥ r⁻_ε}`. In the example, `Γ(h)` is the right derivative of the
anchored revenue along the revenue-preserving curve (the closed formula uses `f(r)` and `φ(r)`,
which jump at `0.3`), the existence of the `ε` with `r⁻_ε = 0.3` and Section 3's `R_2(0) < τ` are
conclusions, and the regularity of the density is a conclusion. -/
theorem theorem_3_6 :
    (∀ (f : ℝ → ℝ) (n : ℕ), 2 ≤ n → IsValueDensity f → IsRegular f →
      ∀ ε : ℝ, 0 < ε → ε < 1 → revCurve f n 0 < (1 - ε) * optRevenue f n →
      0 < rMinus f n ε → rMinus f n ε < rStar f →
      (∃ U ∈ 𝓝 (rMinus f n ε), ∃ K₁ K₂ : NNReal,
        LipschitzOnWith K₁ f U ∧ LipschitzOnWith K₂ (virtualValue f) U) →
      (∃ h₀ > 0, ∀ h ∈ Ioo (0:ℝ) h₀,
        (∃ δ > 0, ∃ r' : ℝ → ℝ,
          IsRevPreserving f n ((1 - ε) * optRevenue f n) (rMinus f n ε) h δ r' ∧
          ContinuousWithinAt r' (Ici 0) 0) ∧
        ∀ δ > 0, ∀ r' : ℝ → ℝ,
          IsRevPreserving f n ((1 - ε) * optRevenue f n) (rMinus f n ε) h δ r' →
          ContinuousWithinAt r' (Ici 0) 0 →
          HasDerivWithinAt (fun ρ => revAnc f n (twoTier (rMinus f n ε) h ρ (r' ρ)))
            (gammaH f n (rMinus f n ε) h) (Ici 0) 0) ∧
      (fun h => gammaH f n (rMinus f n ε) h
          - n * rMinus f n ε * oppCdf f n (rMinus f n ε) * f (rMinus f n ε) * h)
        =O[𝓝[>] 0] (fun h => h ^ 2) ∧
      (∀ᶠ h in 𝓝[>] 0, 0 < gammaH f n (rMinus f n ε) h) ∧
      (∃ π : ℝ → ℝ, IsGradedReserve π ∧ IsTauAdmissible f n ((1 - ε) * optRevenue f n) π ∧
        revAnc f n (fun b => if rMinus f n ε ≤ b then 1 else 0) < revAnc f n π)) ∧
    (IsValueDensity exampleDensity ∧ IsRegular exampleDensity ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ rMinus exampleDensity 2 ε = 3 / 10 ∧
        revCurve exampleDensity 2 0 < (1 - ε) * optRevenue exampleDensity 2 ∧
        3 / 10 < rStar exampleDensity ∧
        ∃ h₀ > 0, ∃ Γ : ℝ → ℝ,
          (∀ h ∈ Ioo (0:ℝ) h₀,
            (∃ δ > 0, ∃ r' : ℝ → ℝ,
              IsRevPreserving exampleDensity 2 ((1 - ε) * optRevenue exampleDensity 2)
                (3 / 10) h δ r' ∧ ContinuousWithinAt r' (Ici 0) 0) ∧
            ∀ δ > 0, ∀ r' : ℝ → ℝ,
              IsRevPreserving exampleDensity 2 ((1 - ε) * optRevenue exampleDensity 2)
                (3 / 10) h δ r' →
              ContinuousWithinAt r' (Ici 0) 0 →
              HasDerivWithinAt (fun ρ => revAnc exampleDensity 2 (twoTier (3 / 10) h ρ (r' ρ)))
                (Γ h) (Ici 0) 0) ∧
          Tendsto (fun h => Γ h / h) (𝓝[>] 0) (𝓝 (-9 / 2800))) := by sorry

end GradedReserve.Supplement
