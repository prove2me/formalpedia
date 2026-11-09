-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_lemma_11
-- name    : GaussProcSparsify.Optimal.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:05.496112+00:00
-- url     : https://prove2.me/theorems/73d686ab-85c7-47d8-8a1e-30cd0d2dc0f8
-- title:
--   Lemma 11 — Shifts keep the softmax within ε in L² (with fixed-point shifts zero)
-- statement:
--   Let $T\subseteq\mathbb R^n$ be finite and nonempty, let $\varepsilon>0$, and let $S\subseteq\mathbb R^n$ be arbitrary. Suppose $\Pi:T\to S$ satisfies $\|t-\Pi(t)\|_2\le\varepsilon$ for every $t\in T$. Set $u_t=t-\Pi(t)$ and $v_t(\theta)=t-\theta u_t$. For every $\beta>0$ there are absolutely continuous real shifts $a_t$ with $a_t(0)=0$ such that
--   $$\|H_1-H_0\|_{L^2(\gamma_n)}\le\varepsilon,$$
--   where $H$ is the shared softmax of $v$ and $a$. In addition, $\Pi(t)=t$ implies $a_t(\theta)=0$ for all $\theta\in[0,1]$. The set $S$ need not be contained in $T$, and no fixed-point hypothesis on $\Pi$ is required.
--
--   The additional conclusion exports a property of the paper's construction that is used later to obtain nonnegative final shifts. The printed approximation bound is retained with its exact constant, uniformly in $\beta$ and the cardinality of $T$.
--
--   Differences from the source:
--   - generalization: existence of shifts with initial value zero and $\|H_1-H_0\|_2\le\varepsilon$ → the same conclusions plus $a_t\equiv0$ whenever $\Pi(t)=t$; reason: the construction has $u_t=0$, hence $m_t=0$, at fixed points; PDF p. 19 uses this property to obtain nonnegative final shifts; dropping the added conjunct recovers the printed lemma
--   - encoding: paths defined on $[0,1]$, with derivatives for almost every parameter → functions on $\mathbb R$ constrained on $[0,1]$, and Lebesgue measure restricted to that interval; reason: every interval path admits an extension, and endpoints are null, so ambient derivatives and derivatives within the interval agree almost everywhere
--   - encoding: $\mathbb R^n$ with the Euclidean norm and standard Gaussian law → `EuclideanSpace ℝ (Fin n)` and `stdGaussian`, including $n=0$; reason: these give the same inner product, norm and Gaussian distribution
--   - encoding: the $L^2(\gamma_n)$ norm → `eLpNorm` with exponent 2 and finite right-hand side; reason: this is the same norm and retains infinite errors rather than collapsing a nonintegrable square to zero
--   - encoding: $T$ finite and non-empty, and $\Pi:T\to S$ → `T : Finset (Vec n)` with `T.Nonempty`, `proj : T → S` between subtypes, and the softmax indexed by the subtype of $T$; reason: these are the same finite family and the same map
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 11 and equation (10), PDF p. 14 (printed p. 13); fixed-point conclusion from the construction, PDF p. 19 (printed p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Softmax

open MeasureTheory

namespace GaussProcSparsify.Optimal

/-- Lemma 11, PDF p. 14, additionally exporting the fixed-point property of its
construction, used on PDF p. 19 to obtain nonnegative final shifts. -/
theorem lemma_11 {n : ℕ} (T : Finset (Vec n)) (hT : T.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (S : Set (Vec n)) (proj : T → S)
    (hproj : ∀ t : T, ‖(t : Vec n) - (proj t : Vec n)‖ ≤ ε)
    (β : ℝ) (hβ : 0 < β) :
    ∃ a : T → ℝ → ℝ,
      (∀ t, AbsolutelyContinuousOnInterval (a t) 0 1) ∧
      (∀ t, a t 0 = 0) ∧
      (∀ t : T, (proj t : Vec n) = (t : Vec n) →
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, a t θ = 0) ∧
      eLpNorm (fun g =>
        softmax β (fun (t : T) θ => (t : Vec n) - θ • ((t : Vec n) - (proj t : Vec n))) a 1 g -
        softmax β (fun (t : T) θ => (t : Vec n) - θ • ((t : Vec n) - (proj t : Vec n))) a 0 g)
        2 (gaussian n) ≤ ENNReal.ofReal ε := by sorry

end GaussProcSparsify.Optimal
