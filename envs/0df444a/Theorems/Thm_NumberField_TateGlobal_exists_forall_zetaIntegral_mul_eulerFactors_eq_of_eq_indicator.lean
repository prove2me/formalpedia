-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator
-- name    : NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/caf93cb6-50cd-51a9-9c15-39f282bded35
-- title:
--   Euler product of the global Tate zeta integral (S-form)
-- statement:
--   Let $F$ be a number field, let the idele group $(\mathbb{A}_F)^\times$ carry a measurable structure that is the Borel structure of its topology together with a Haar measure $\nu$, let $S$ be a finite set of finite places of $F$ (height one primes of $\mathcal{O}_F$), let each completion $F_v$ carry its Borel structure and an additive Haar measure $\mu_f(v)$, and let $\varpi_v \in F_v^\times$ satisfy $v(\varpi_v) = \mathrm{ofAdd}(-1)$, i.e. be a uniformiser. The assertion is that there exists a function $A$ of three arguments — a function $G$ on the infinite adeles, a multiplicative character $\chi : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$, and a complex number $s$, and of nothing else — such that for every $f : \mathbb{A}_F \to \mathbb{C}$, every $G$, and every family $h_v : F_v \to \mathbb{C}$ with $f$ equal to the indicator, on the set of adeles whose finite component lies in $\mathcal{O}_v$ for all $v \notin S$, of $x \mapsto G(x_\infty)\prod_{v\in S} h_v(x_v)$ (so $f$ vanishes off that set), for every continuous $\chi$ with $\lVert\chi(x)\rVert = 1$ for all $x$ and with the local character $\chi_v$ (the restriction of $\chi$ along $F_v^\times \to (\mathbb{A}_F)^\times$) trivial on the units of $\mathcal{O}_v$ for each $v \notin S$, and for every $s$ with $\operatorname{Re} s > 1$, one has
--   $$\Big(\int f(x)\,\chi(x)\,\lvert x\rvert^{s}\,d\nu\Big)\cdot\prod_{v\notin S}\big(1-\chi_v(\varpi_v)\,N(v)^{-s}\big) = A(G,\chi,s)\cdot\prod_{v\in S} Z_v(h_v,\chi_v,s),$$
--   where $\lvert x\rvert$ is the idele norm given by the scaling factor of $x$ on Haar measure of $\mathbb{A}_F$, $N(v)$ is the absolute norm of the prime $v$, the product over $v \notin S$ is an unconditional infinite product over the places outside $S$, and $Z_v(h_v,\chi_v,s)=\int h_v\,\tilde{\chi_v}\,\lvert\cdot\rvert_v^{s}$ against $\mu_f(v)$ restricted to $F_v\setminus\{0\}$ with density $\lvert\cdot\rvert_v^{-1}$, with $\tilde{\chi_v}$ the extension of $\chi_v$ by $0$ at $0$. No integrability is assumed: all integrals are Bochner integrals with the usual convention at non-integrable integrands, $f$ need not be Schwartz–Bruhat, and $\chi$ is not required to be trivial on $F^\times$.
--
--   This is the $S$-truncated Euler factorisation of Tate's global zeta integral: the zeta integral of a function that is a product of an archimedean factor and finitely many local factors, times the unramified Euler factors outside $S$, splits into a term depending only on the archimedean data $(G,\chi,s)$ and the local Tate zeta integrals at the places of $S$. It is invoked in the analytic estimates for the twisted unipotent term, where the dependence of the archimedean contribution on $G$, $\chi$ and $s$ alone is what is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ A : (InfiniteAdeleRing F → ℂ) → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) → ℂ → ℂ,
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (G : InfiniteAdeleRing F → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : ∀ x, f x = (integralOutside S).indicator
          (fun x => G x.1 * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = A G χ s * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s := by sorry
