-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_indicator_setOf_valued_sub_one_le
-- name    : LanglandsTunnell.TateLocal.localZeta_tateFourier_indicator_setOf_valued_sub_one_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e39c25f5-f365-56e2-b0c8-db7882ffb7f7
-- title:
--   Ramified local zeta integral of a Fourier-transformed ball indicator
-- statement:
--   Let $K$ be a number field, $v$ a maximal ideal of $\mathcal{O}_K$, and $K_v$ the $v$-adic completion, equipped with a Borel measurable structure and an additive Haar measure $\mu$; write $|\cdot|_v$ for its valuation with values in $\{0\}\cup\exp(\mathbb{Z})$, $\varpi_v$ for the unit `uniformizerUnit K v` of $K_v$ attached to the chosen uniformizer of $v$, and $Nv$ for the absolute norm of $v$. Let $\psi\colon K_v\to\mathbb{C}$ be an additive character and $n\in\mathbb{Z}$ such that $\psi(x)=1$ whenever $|x|_v\le\exp n$, while $\psi(x)\ne1$ for at least one $x$ with $|x|_v\le\exp(n+1)$. Let $\chi\colon K_v^\times\to\mathbb{C}^\times$ be a multiplicative character and $a\ge1$ a natural number with `HasConductorExponentAt K v χ a`, i.e. $\chi(u)=1$ for every unit $u$ with $|u|_v=1$ and $|u-1|_v\le\exp(-a)$, and for every $m<a$ some unit $u$ with $|u|_v=1$ and ($m=0$ or $|u-1|_v\le\exp(-m)$) has $\chi(u)\ne1$. Let $s\in\mathbb{C}$ satisfy $\|\chi^{-1}(\varpi_v)\,Nv^{-(1-s)}\|<1$. Then the local zeta integral $\int f(x)\,\chi^{-1}(x)\,|x|_v^{1-s}\,d^\times x$, taken against the multiplicative measure $|x|_v^{-1}d\mu$ on $K_v\setminus\{0\}$ with $\chi^{-1}$ extended by $0$ at $0$, of the Fourier transform $f(y)=\int \mathbf{1}_{\{|x-1|_v\le\exp(-a)\}}\,\psi(xy)\,d\mu(x)$ equals $$\mu\bigl(\{|x|_v\le\exp(-a)\}\bigr)\cdot\chi(\varpi_v)^{n+a}\cdot\bigl(Nv^{\,n+a}\bigr)^{1-s}\int_{\{|u|_v=1\}}\psi\bigl(\varpi_v^{-(n+a)}u\bigr)\,\chi^{-1}(u)\,d\mu(u),$$ where $|\cdot|_v$ in the zeta integral denotes the module (`modulus`) of $K_v$.
--
--   This is Tate's local computation at a ramified place: the zeta integral of the Fourier transform of the indicator of the ball $1+\mathfrak{p}_v^a$ is expressed, for an additive character of exact level $n$ and a character of conductor exponent $a\ge1$, as an explicit constant times a Gauss sum over the units. It feeds the evaluation of the local zeta integral of the standard test function at $v$, [`LanglandsTunnell.TateLocal.localZeta_tateFourier_stdTestFunAt`](thm.html#LanglandsTunnell.TateLocal.localZeta_tateFourier_stdTestFunAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_indicator_setOf_valued_sub_one_le.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel

theorem LanglandsTunnell.TateLocal.localZeta_tateFourier_indicator_setOf_valued_sub_one_le (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a) (s : ℂ)
    (hs : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))‖ < 1) :
    localZeta μ (tateFourier ψ μ
        ({x : v.adicCompletion K | Valued.v (x - 1) ≤ WithZero.exp (-(a : ℤ))}.indicator fun _ => (1 : ℂ)))
        χ⁻¹ (1 - s)
      = ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(a : ℤ))} : ℝ) : ℂ)
          * (χ (uniformizerUnit K v) : ℂ) ^ (n + a : ℤ)
          * ((((Ideal.absNorm v.asIdeal : ℝ) ^ (n + a : ℤ) : ℝ) : ℂ)) ^ (1 - s)
          * ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
              ψ (((uniformizerUnit K v ^ (-(n + a : ℤ)) : (v.adicCompletion K)ˣ) : v.adicCompletion K) * u)
                * charExt χ⁻¹ u ∂μ := by sorry
