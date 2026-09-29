-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/6422a484-b386-516f-80b7-4aa62f2f1585
-- title:
--   Finite Fourier inversion on a valuation shell
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$ carrying its valuation with values in $\mathbb{Z}$ adjoined $0$ written multiplicatively, and let $\psi_v$ be a complex additive character of $\mathbb{Q}_v$ that is nontrivial and is trivial on some ball $\{x : |x| \le \exp(n)\}$, $n \in \mathbb{Z}$. Fix $k \in \mathbb{Z}$, a natural number $m$, and a function $h : \mathbb{Q}_v^{\times} \to \mathbb{C}$ satisfying: for all units $a, b$ with $|a| = \exp(-k)$ and $|b - 1| \le \exp(-(m+1))$ one has $h(ab) = h(a)$. Assume further that, with $\mathbb{Q}_v$ given its Borel $\sigma$-algebra, for every $y \in \mathbb{Q}_v$ the integral of $a \mapsto \psi_v(ya)\,h(a)$ over the shell $\{a \in \mathbb{Q}_v^{\times} : |a| = \exp(-k)\}$ vanishes, the measure being the pullback along $\mathbb{Q}_v^{\times} \hookrightarrow \mathbb{Q}_v$ of the multiplicative measure $d^{\times}x = |x|^{-1}\,dx$ (the restriction of $dx$ to $\mathbb{Q}_v \setminus \{0\}$ weighted by the inverse of the module $|x|$, the latter defined as the scaling factor of $dx$ under multiplication by $x$), where $dx$ is the additive Haar measure giving the local integers the mass $(\mathrm{N}v)^{-\ell/2}$ with $\ell$ the level of the standard local additive character at $v$. Then $h(a) = 0$ for every unit $a$ with $|a| = \exp(-k)$.
--
--   This is a finite Fourier inversion, or injectivity, statement: a function on a valuation shell which is invariant under a group of higher units and all of whose additive twists integrate to zero must vanish on that shell. It serves as the injectivity step in the proof of non-vanishing of the local $GL_3 \times GL_1$ zeta integrals used in the cubic-induction part of the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (hψloc : ∃ n : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψv x = 1)
    (k : ℤ) (h : (v.adicCompletion ℚ)ˣ → ℂ) (m : ℕ)
    (hloc : ∀ a b : (v.adicCompletion ℚ)ˣ, Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k) →
      Valued.v ((b : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((m : ℤ) + 1)) → h (a * b) = h a)
    (hzero : letI := localBorel ℚ v
      ∀ y : v.adicCompletion ℚ,
        ∫ a in {a : (v.adicCompletion ℚ)ˣ | Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k)},
          ψv (y * (a : v.adicCompletion ℚ)) * h a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0) :
    ∀ a : (v.adicCompletion ℚ)ˣ, Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k) → h a = 0 := by sorry
