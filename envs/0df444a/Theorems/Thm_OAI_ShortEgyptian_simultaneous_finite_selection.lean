-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_simultaneous_finite_selection
-- name    : OAI.ShortEgyptian.simultaneous_finite_selection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:16:22.033982+00:00
-- url     : https://prove2.me/theorems/c525ae58-5b42-4a4b-8b0d-c54cb7bc3af9
-- title:
--   Probabilistic selection of a tuple that meets finitely many mean bounds and avoids finitely many events
-- statement:
--   Let $\Omega$ be a finite nonempty set and let $J$, $D$, $U$ be finite sets; $\mathbb{E}_\omega$ and $\Pr_\omega$ refer to the uniform distribution on $\Omega$. Fix $j_0\in J$ and let
--
--   - $B\colon D\times\Omega\to\mathbb{R}$ with $B(d,\omega)\ge0$, $c\colon D\to\mathbb{R}$ with $c(d)>0$, and $\varepsilon\colon D\to\mathbb{R}$;
--   - $P_u\subseteq\Omega$ ($u\in U$) be events and $r\colon U\to\mathbb{R}$.
--
--   Assume that
--
--   $$\mathbb{E}_\omega B(d,\omega)\le c(d)\,\varepsilon(d)\quad(d\in D),\qquad \Pr_\omega[\omega\in P_u]\le r(u)\quad(u\in U),\qquad \sum_{d\in D}\varepsilon(d)+\sum_{u\in U}r(u)^{|J|}<1 .$$
--
--   Then there is a tuple $f\colon J\to\Omega$ with the following two properties.
--
--   1. The distinguished coordinate satisfies all the bounds:
--
--      $$
--      B\bigl(d,f(j_0)\bigr)<c(d)\qquad\text{for every } d\in D .
--      $$
--
--   2. Every event is avoided by some coordinate: for every $u\in U$ there is $j\in J$ with $f(j)\notin P_u$.
--
--   This packages a first-moment (probabilistic method) argument for $|J|$ independent uniform samples. The distinguished sample $f(j_0)$ makes each nonnegative quantity $B(d,\cdot)$ small, and every bad event $P_u$ is avoided by at least one sample, since all $|J|$ samples fail with probability at most $r(u)^{|J|}$. It is used to choose finitely many random prime-product lists such that the first list has few Fourier-bad moduli at every scale and every modulus in a prescribed finite set is good for at least one list.
--
--   **Formalization Note** The events are predicates `P : U → Ω → Prop`, probabilities are averages `𝔼 ω` of `if … then 1 else 0` indicators, and $f$ ranges over functions `J → Ω`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean#L153-L197

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection

open OAI OAI.ShortEgyptian
universe uI uΩ uJ uA uE uD uU
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.simultaneous_finite_selection {Ω : Type uΩ} {J : Type uJ} {D : Type uD} {U : Type uU}
    [Fintype Ω] [Nonempty Ω] [Fintype J] [Fintype D] [Fintype U]
    (j₀ : J) (B : D → Ω → ℝ) (c ε : D → ℝ) (P : U → Ω → Prop) (r : U → ℝ)
    (hB : ∀ d ω, 0 ≤ B d ω) (hc : ∀ d, 0 < c d)
    (hmean : ∀ d, (𝔼 ω, B d ω) ≤ c d*ε d)
    (hprob : ∀ u, (𝔼 ω, if P u ω then (1:ℝ) else 0) ≤ r u)
    (hsmall : (∑ d, ε d)+(∑ u, r u^Fintype.card J) < 1) :
    ∃ f : J → Ω, (∀ d, B d (f j₀) < c d) ∧ (∀ u, ∃ j, ¬P u (f j)) := by sorry
