-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_indicator_setOf_valued_sub_le
-- name    : LanglandsTunnell.TateLocal.tateFourier_tateFourier_indicator_setOf_valued_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/29ad1a07-06ff-5a77-9654-10ef9e2148df
-- title:
--   Double Tate transform of a ball indicator on Kᵥ
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of $\mathcal{O}_K$, and $K_v =$ `v.adicCompletion K` its completion, carrying the valuation `Valued.v` with values in $\{0\}\cup\exp(\mathbb{Z})$, equipped with a measurable-space structure that is the Borel structure of its topology; let $\mu$ be an additive Haar measure on $K_v$, let $\psi$ be an additive character $K_v \to \mathbb{C}^\times$, and let $n \in \mathbb{Z}$ be such that $\psi(x)=1$ for all $x$ with $|x|_v \le \exp n$, while $\psi(x_1) \ne 1$ for at least one $x_1$ with $|x_1|_v \le \exp(n+1)$. For $f : K_v \to \mathbb{C}$ the transform is $(\mathrm{tateFourier}\,\psi\,\mu\,f)(y) = \int_{K_v} f(x)\,\psi(xy)\,d\mu(x)$. Then for all $a \in K_v$, $m \in \mathbb{Z}$ and $x \in K_v$, applying this transform twice to the characteristic function (complex-valued, via `Set.indicator`) of the ball $\{x' : |x'-a|_v \le \exp(-m)\}$ and evaluating at $x$ gives
--   $$N(v)^{\,n}\,\mu(\mathcal{O}_v)^2 \cdot \mathbf{1}_{\{x' : |x'+a|_v \le \exp(-m)\}}(x),$$
--   where $N(v) =$ `Ideal.absNorm v.asIdeal`, the real power $N(v)^n$ is an integer power, $\mu(\mathcal{O}_v)$ is the real-valued measure of the unit ball `v.adicCompletionIntegers K`, and the real scalar is viewed in $\mathbb{C}$.
--
--   This is the Fourier inversion formula of local Tate theory in the concrete case of ball indicators: iterating the $\psi$-transform returns the indicator of the reflected ball, up to the constant $N(v)^n\mu(\mathcal{O}_v)^2$ attached to the pair $(\psi,\mu)$. It feeds the inversion statement for Schwartz–Bruhat functions on $K_v$, [`LanglandsTunnell.TateLocal.tateFourier_tateFourier_of_isSchwartzBruhat`](thm.html#LanglandsTunnell.TateLocal.tateFourier_tateFourier_of_isSchwartzBruhat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_indicator_setOf_valued_sub_le.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.tateFourier_tateFourier_indicator_setOf_valued_sub_le (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (a : v.adicCompletion K) (m : ℤ) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ
        ({x' : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-m)}.indicator fun _ => (1 : ℂ))) x
      = (((Ideal.absNorm v.asIdeal : ℝ) ^ n
            * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 : ℝ) : ℂ)
          * {x' : v.adicCompletion K | Valued.v (x' + a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x := by sorry
