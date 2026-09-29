-- Prove2me | Theorems.Thm_LogDerivZetaHolcLargeT
-- name    : LogDerivZetaHolcLargeT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:59:57.276847+00:00
-- url     : https://prove2.me/theorems/944d5729-9176-47a7-a304-56026a1ef477
-- title:
--   Holomorphy of $\zeta'/\zeta$ on tall rectangles $[1-A/(\log T)^9,\,2]\times[-T,T]$ away from $s=1$
-- statement:
--   There exists a constant $A\in(0,\tfrac12]$ such that for every height $T\ge 3$, the logarithmic derivative of the Riemann zeta function
--
--   $$s \longmapsto \frac{\zeta'(s)}{\zeta(s)}$$
--
--   is holomorphic on the punctured rectangle
--
--   $$\left(\left[\,1-\frac{A}{(\log T)^{9}},\ 2\,\right]\times[-T,\,T]\right)\setminus\{1\},$$
--
--   i.e. on the set of $s=\sigma+it$ with $1-A/(\log T)^9\le\sigma\le 2$ and $|t|\le T$, excluding the pole of $\zeta$ at $s=1$.
--
--   The content is the zero-free region: since $\zeta$ has no zeros in this rectangle (with $A$ coming from the classical de la Vallée-Poussin-type region, in the $(\log T)^9$-width form used in this development) and its only pole there is at $s=1$, the quotient $\zeta'/\zeta$ is holomorphic off $s=1$.
--
--   This holomorphy statement licenses the contour-pulling step in the proof of the Prime Number Theorem with error term: the integration contour at $\operatorname{Re} s=1+\delta$ can be moved left into the rectangle up to height $T$, with the residue at $s=1$ producing the main term $X$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2726-L2769

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

theorem LogDerivZetaHolcLargeT :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 9) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by sorry
