-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_7_7
-- name    : MetricMinTest.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:46:47.600413+00:00
-- url     : https://prove2.me/theorems/f70dd772-491c-4654-94da-58ee9ab894a9
-- title:
--   Theorem 7.7, p.19 — regional composition beats every single cover by $\Omega(\log n/\log\log n)$
-- statement:
--   For every integer $m\ge1$ and $\gamma\in(0,1/4]$ there is a metric $\tilde d_m$ on $n=\Theta(16^m)$ points for which, writing $K=4^m$ and $D_m=1+3m/4$,
--   $$H_{\tilde d_m}(\gamma)=\Theta\Big(\frac{K}{\gamma^2D_m}\Big),\qquad J_{\tilde d_m}(\gamma)=\Theta\Big(\frac{K(1+\ln D_m)}{\gamma^2D_m}\Big),$$
--   $$\min\Big\{F_{\tilde d_m}(\gamma),\ \inf_{(Z,r):S(Z,r)=[n]}H_{Z,r}(1+\ln\rho_{Z,r})\Big\}=\Theta(K\gamma^{-2}).$$
--   Thus, at constant confidence, fractional composition improves the best of all single-cover screening bounds and the global ball-certificate bound by a factor $\Omega(\log n/\log\log n)$. In particular, the best single-cover expression does not characterize $C^\star_d$ or $B^\star_d$ within an absolute constant factor.
--
--   The example glues the critical ultrametric to a graph metric, so that the two components favour different strategies and only a regional mixture is efficient on both.
--
--   **Formalization Note** All $\Theta$ and $\Omega$ use absolute constants. The last sentence is stated at every fixed $\delta\in(0,1/4]$: $C^\star$ and $B^\star$ of $\tilde d_m$ are eventually (in $m$, uniformly in $\gamma$) at most any $\varepsilon>0$ times $\inf_{(Z,r)}H_{Z,r}(\ln(1/\delta)+\ln\rho_{Z,r})$.
--
--   Differences from the source:
--   - encoding: $n=\Theta(16^m)$ and the three $\Theta$'s → explicit constants $c,C>0$ quantified before every variable they must not depend on; reason: the paper's convention for $\asymp$, $O$, $\Theta$, $\Omega$ (§2, p.6)
--   - encoding: for every $m$, $\gamma$ there is a metric $\tilde d_m$ → point counts $n(m)$ and metrics $d(m,\gamma)$ on $\mathrm{Fin}\,n(m)$ chosen as functions, so that the asymptotic clauses refer to one family; reason: the clauses "Thus" and "In particular" are statements about the family
--   - reading: improves … by a factor $\Omega(\log n/\log\log n)$ → $c\,(\ln n/\ln\ln n)\,J\le\min\{F,\Sigma\}$ with an absolute $c>0$; reason: the improvement is the ratio of the single-cover and ball bounds to $J$, the factor of the regional bound
--   - generalization: the best single-cover expression does not characterize $C^\star_d$ or $B^\star_d$ within an absolute constant factor → at every fixed $\delta\in(0,1/4]$, for every $\varepsilon>0$, eventually in $m$ and uniformly in $\gamma$: $C^\star,B^\star\le\varepsilon\inf_{(Z,r)}H_{Z,r}(\ln(1/\delta)+\ln\rho_{Z,r})$; reason: the ratio tends to $0$ (the proof, p.20, shows it is unbounded via $H_{Z,r}(\ln(1/\delta)+\ln\rho_{Z,r})$); this implies that no positive constant bounds it below
--   - encoding: a metric → a pseudometric with $d(i,j)=0\Rightarrow i=j$; reason: definition of a metric
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 7.7, p.19

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Bstar
import Definitions.Def_MetricMinTest_Supplement_Cstar
import Definitions.Def_MetricMinTest_Supplement_mixedWorkload
import Definitions.Def_MetricMinTest_Supplement_singleCoverInf

namespace MetricMinTest.Supplement

/-- **Theorem 7.7 (Regional composition beats every single cover).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 7.7, p.19: "For
every integer m ≥ 1 and γ ∈ (0, 1/4], there is a metric d̃_m on n = Θ(16^m) points for which,
writing K = 4^m and D_m = 1 + 3m/4, H_{d̃_m}(γ) = Θ(K/(γ²D_m)),
J_{d̃_m}(γ) = Θ(K(1 + ln D_m)/(γ²D_m)),
min{F_{d̃_m}(γ), inf_{(Z,r):S(Z,r)=[n]} H_{Z,r}(1 + ln ρ_{Z,r})} = Θ(Kγ⁻²). Thus, at constant
confidence, fractional composition improves the best of all single-cover screening bounds and the
global ball-certificate bound by a factor Ω(log n/ log log n). In particular, the best single-cover
expression does not characterize C⋆_d or B⋆_d within an absolute constant factor."

**Formalization Note.** The family is existential: point counts `n m` and metrics `d m γ` on
`Fin (n m)` (a metric: pseudometric with `d i j = 0 → i = j`). Every `Θ` and the `Ω` use
absolute constants `c, C > 0` chosen before `m, γ`. The `Ω` clause is
`c (ln n / ln ln n) J ≤ min{F, single}`. "Does not characterize C⋆ or B⋆": at every fixed
`δ ∈ (0, 1/4]`, the ratio of `C⋆` (and of `B⋆`) to the best single-cover expression at that
confidence, `inf H_{Z,r}(ln(1/δ) + ln ρ_{Z,r})` (the form used in the proof, p.20), tends to `0`
along the family, uniformly in `γ`; in particular no positive constant bounds it below. -/
theorem theorem_7_7 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ (n : ℕ → ℕ) (d : (m : ℕ) → ℝ → Fin (n m) → Fin (n m) → ℝ),
      (∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        IsPseudometric (d m γ) ∧ (∀ i j, d m γ i j = 0 → i = j) ∧
        c * (16 : ℝ) ^ m ≤ (n m : ℝ) ∧ (n m : ℝ) ≤ C * (16 : ℝ) ^ m ∧
        c * ((4 : ℝ) ^ m / (γ ^ 2 * (1 + 3 * (m : ℝ) / 4))) ≤ infoWorkload (d m γ) γ ∧
        infoWorkload (d m γ) γ ≤ C * ((4 : ℝ) ^ m / (γ ^ 2 * (1 + 3 * (m : ℝ) / 4))) ∧
        c * ((4 : ℝ) ^ m * (1 + Real.log (1 + 3 * (m : ℝ) / 4)) /
            (γ ^ 2 * (1 + 3 * (m : ℝ) / 4))) ≤ mixedWorkload (d m γ) γ ∧
        mixedWorkload (d m γ) γ ≤ C * ((4 : ℝ) ^ m * (1 + Real.log (1 + 3 * (m : ℝ) / 4)) /
            (γ ^ 2 * (1 + 3 * (m : ℝ) / 4))) ∧
        c * ((4 : ℝ) ^ m * (γ ^ 2)⁻¹) ≤
          min (certWorkload (d m γ) γ) (singleCoverInf (d m γ) γ 1) ∧
        min (certWorkload (d m γ) γ) (singleCoverInf (d m γ) γ 1) ≤
          C * ((4 : ℝ) ^ m * (γ ^ 2)⁻¹) ∧
        c * (Real.log (n m) / Real.log (Real.log (n m))) * mixedWorkload (d m γ) γ ≤
          min (certWorkload (d m γ) γ) (singleCoverInf (d m γ) γ 1)) ∧
      (∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) (1 / 4) → ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 1 ≤ m →
        ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
          Cstar (d m γ) γ δ ≤
            ENNReal.ofReal (ε * singleCoverInf (d m γ) γ (Real.log (1 / δ))) ∧
          Bstar (d m γ) γ δ ≤
            ENNReal.ofReal (ε * singleCoverInf (d m γ) γ (Real.log (1 / δ)))) := by sorry

end MetricMinTest.Supplement
