-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_eq_of_isSchwartzBruhat
-- name    : LanglandsTunnell.TateLocal.tateFourier_tateFourier_eq_of_isSchwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/a0b4a7cd-071a-53cc-bd1e-d343bd2ca6b2
-- title:
--   Local Fourier inversion at a finite place
-- statement:
--   Let $K$ be a number field and $v$ a point of the height-one spectrum of its ring of integers $\mathcal{O}_K$, and let $K_v$ denote the $v$-adic completion, equipped with a measurable space structure that is the Borel structure of its topology. Let $\mu$ be an additive Haar measure on $K_v$, let $\psi \colon K_v \to \mathbb{C}$ be an additive character, and let $n \in \mathbb{Z}$. Assume that $\psi$ is trivial on the set of $x$ with $\mathrm{v}(x) \le \exp(n)$, i.e. on the fractional ideal $\mathfrak{p}_v^{-n}$ (hypothesis `hψn`), and that there exists $x$ with $\mathrm{v}(x) \le \exp(n+1)$, i.e. $x \in \mathfrak{p}_v^{-n-1}$, such that $\psi(x) \ne 1$ (hypothesis `hψn'`); thus $\psi$ has exact level $n$ in this normalisation. Let $f \colon K_v \to \mathbb{C}$ be locally constant with compact support, and let $x \in K_v$. Writing $(\mathrm{tateFourier}\ \psi\ \mu\ g)(y) = \int_{K_v} g(z)\,\psi(zy)\,d\mu(z)$, the assertion is that applying this transform twice to $f$ and evaluating at $x$ gives $\mu(\{y : \mathrm{v}(y) \le 1\})\,\mu(\{y : \mathrm{v}(y) \le \exp(n)\})\,f(-x)$, the two real measures of the valuation ring $\mathcal{O}_v$ and of $\mathfrak{p}_v^{-n}$ being coerced into $\mathbb{C}$.
--
--   This is the local Fourier inversion formula at a finite place in Tate's local theory, with the normalising constant $\mu(\mathcal{O}_v)\mu(\mathfrak{p}_v^{-n})$ recorded explicitly for an arbitrary Haar measure and an arbitrary character with open kernel; in particular $\mu$ is self-dual for $\psi$ exactly when this constant is $1$. It rests on the computation of the transform of the indicator function of a ball, [`LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le`](thm.html#LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le), and is used to verify the inversion property for the standard local character and the self-dual measure over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_eq_of_isSchwartzBruhat.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.tateFourier_tateFourier_eq_of_isSchwartzBruhat (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (f : v.adicCompletion K → ℂ) (hf : IsSchwartzBruhat f) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ f) x =
      ((μ.real {y : v.adicCompletion K | Valued.v y ≤ 1} : ℝ) : ℂ) *
        ((μ.real {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp n} : ℝ) : ℂ) * f (-x) := by sorry
