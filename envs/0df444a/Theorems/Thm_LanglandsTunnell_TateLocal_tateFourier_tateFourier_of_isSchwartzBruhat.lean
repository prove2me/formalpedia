-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_of_isSchwartzBruhat
-- name    : LanglandsTunnell.TateLocal.tateFourier_tateFourier_of_isSchwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/a94ec558-a552-5f95-994a-17ee7d52f4e7
-- title:
--   Fourier inversion for Schwartz–Bruhat functions on Kᵥ
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of its ring of integers $\mathcal{O}_K$, and $K_v =$ `v.adicCompletion K` the associated completion, carrying its valuation $|\cdot|_v$ with values in $\{0\}\cup\exp(\mathbb{Z})$, equipped with a measurable space structure that is the Borel one, and let $\mu$ be an additive Haar measure on $K_v$. Let $\psi$ be an additive character of $K_v$ with values in $\mathbb{C}$ and $n$ an integer such that $\psi(x) = 1$ for every $x$ with $|x|_v \le \exp n$, while there exists $x$ with $|x|_v \le \exp(n+1)$ and $\psi(x) \ne 1$; thus $\psi$ has exact level $n$. For $f : K_v \to \mathbb{C}$ the transform is $(\mathcal{F}_\psi^\mu f)(y) = \int_{K_v} f(x)\,\psi(xy)\,d\mu(x)$. The assertion is that for every $f : K_v \to \mathbb{C}$ which is locally constant and has compact support, and every $x \in K_v$, $$(\mathcal{F}_\psi^\mu(\mathcal{F}_\psi^\mu f))(x) = \bigl(N v\bigr)^{n}\,\mu(\mathcal{O}_v)^{2}\, f(-x),$$ where $N v$ is the absolute norm of the ideal $v$, $\mathcal{O}_v$ is the valuation ring `v.adicCompletionIntegers K` of $K_v$, $\mu(\mathcal{O}_v)$ denotes its real-valued measure, and the real scalar is coerced into $\mathbb{C}$.
--
--   This is local Fourier inversion in Tate's local theory, in the form where the inversion constant is made explicit in terms of the level of $\psi$ and the Haar volume of the ring of integers, and no self-duality normalisation is imposed. It is obtained from the corresponding identity for indicator functions of balls $a + \mathfrak{p}_v^m$, and is used in the specialisation to the self-dual Haar measure, [`LanglandsTunnell.TateLocal.tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat`](thm.html#LanglandsTunnell.TateLocal.tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_of_isSchwartzBruhat.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.tateFourier_tateFourier_of_isSchwartzBruhat (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (f : v.adicCompletion K → ℂ) (hf : IsSchwartzBruhat f) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ f) x
      = (((Ideal.absNorm v.asIdeal : ℝ) ^ n
            * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 : ℝ) : ℂ) * f (-x) := by sorry
