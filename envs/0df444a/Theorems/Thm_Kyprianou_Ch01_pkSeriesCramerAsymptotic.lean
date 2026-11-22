-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pkSeriesCramerAsymptotic
-- name    : Kyprianou.Ch01.pkSeriesCramerAsymptotic
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T09:19:37.360677+00:00
-- url     : https://prove2.me/theorems/0867b143-4951-42ae-887b-0edd5aa700fa
-- title:
--   Cramér asymptotics of the Pollaczek–Khintchine series (analytic core of Thm 1.10(ii))
-- statement:
--   Purely analytic form of Cramér's asymptotic. Let $F$ be a probability law on $(0,\infty)$ with mean $\mu>0$, let $\lambda>0$, $c>0$ with $\rho:=\lambda\mu/c<1$, and let $\eta$ be the integrated-tail law, $\eta([0,x])=\mu^{-1}\int_0^x\overline F(y)\,dy$, carried by $[0,\infty)$. Let $\nu>0$ satisfy the Lundberg equation $\lambda\int(e^{\nu x}-1)\,F(dx)=c\nu$ (with $e^{\nu x}$ $F$-integrable). Define the Pollaczek–Khintchine distribution function
--
--   $$W(x)=(1-\rho)\sum_{k\ge0}\rho^k\,\eta^{*k}\big((-\infty,x]\big).$$
--
--   Then, with $T:=\int_0^\infty y\,e^{\nu y}\,\overline F(y)\,dy\in(0,\infty]$,
--
--   $$\lim_{x\to\infty} e^{\nu x}\big(1-W(x)\big)=\begin{cases}\dfrac{c-\lambda\mu}{\lambda\nu\,T}, & T<\infty,\\[2mm] 0,& T=\infty.\end{cases}$$
--
--   Proof route: $\overline W=1-W$ solves the defective renewal equation $\overline W(x)=\rho\,\overline\eta(x)+\rho\int_0^x\overline W(x-y)\,\eta(dy)$; the Lundberg equation says exactly $\rho\int e^{\nu y}\eta(dy)=1$, so the Esscher-tilted kernel $\rho e^{\nu y}\eta(dy)$ is a proper probability law, which is absolutely continuous (hence non-lattice) with mean $\lambda T/c$. The key renewal theorem applied to $e^{\nu x}\overline W(x)$ with directly Riemann integrable forcing term $\rho e^{\nu x}\overline\eta(x)$, whose integral equals $(c-\lambda\mu)/(c\nu)$, gives the limit. No separate non-lattice hypothesis on $F$ is needed.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, §1.3.1, Theorems 1.8–1.10, pp. 15–18, proof of Theorem 1.10(ii), pp. 17–18 (renewal-equation argument)

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.pkSeriesCramerAsymptotic
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hexpint : Integrable (fun x : ℝ => Real.exp (nu * x)) F)
    (hlundberg :
      (rate : ℝ) * (∫ x, (Real.exp (nu * x) - 1) ∂F) = premium * nu)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (eta (Set.Iic x)).toReal = integratedTailCDF F mu x) :
    let weightedTail : ℝ≥0∞ :=
      ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (y * Real.exp (nu * y) * (F (Set.Ioi y)).toReal) ∂volume
    Tendsto (fun x : ℝ => Real.exp (nu * x) *
      (1 - pkCDF eta ((rate : ℝ) * mu / premium) x)) atTop
      (nhds (if weightedTail = ⊤ then 0 else
        (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) *
          weightedTail.toReal)⁻¹)) := by
  sorry
