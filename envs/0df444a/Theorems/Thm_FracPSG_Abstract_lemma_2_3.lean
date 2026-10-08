-- Prove2me | Theorems.Thm_FracPSG_Abstract_lemma_2_3
-- name    : FracPSG.Abstract.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:36.613623+00:00
-- url     : https://prove2.me/theorems/94b7062e-5418-453e-b9ba-ea582b3a1a1d
-- title:
--   Lemma 2.3 — uniformized KL property along a bounded sequence
-- statement:
--   Let $(x_n)_{n\in\mathbb N}$ be a bounded sequence in a finite-dimensional real Hilbert space $\mathcal H$ and $\Omega$ the set of its cluster points. Let $h:\mathcal H\to(-\infty,+\infty]$ be proper and lower semicontinuous, constant on $\Omega$, and with the Kurdyka–Łojasiewicz (KL) property at each point of $\Omega$. Put $\Omega_0:=\{\bar x\in\Omega: h(x_n)\to h(\bar x)\}$ and suppose $\Omega_0\neq\emptyset$. Then there are $\eta>0$, a desingularizing function $\varphi\in\Phi_\eta$ (continuous and concave on $[0,\eta)$, $\varphi(0)=0$, $C^1$ on $(0,\eta)$ with $\varphi'>0$) and $n_0\in\mathbb N$ such that, for every $\bar x\in\Omega_0$ and every $n\ge n_0$ with $h(x_n)>h(\bar x)$, one has $h(x_n)<h(\bar x)+\eta$ and
--   $$\varphi'\big(h(x_n)-h(\bar x)\big)\,\operatorname{dist}\big(0,\partial_L h(x_n)\big)\ge1. \qquad (9)$$
--
--   The lemma turns the pointwise KL property into a single inequality valid along the tail of the sequence, with one $\varphi$ and one $n_0$ for all of $\Omega_0$; it is the step that feeds the KL property into the finite-length argument of Theorem 5.2.
--
--   **Formalization Note** $\mathcal H$ is `EuclideanSpace ℝ (Fin N)`. The KL property is the published `HasKLProperty`, with $\eta$ a positive real (the paper's $\eta=+\infty$ can always be shrunk) and no requirement $\bar x\in\operatorname{dom}\partial_L h$, so the hypothesis is at most as strong as the paper's. (9) is stated as $1\le\varphi'(h(x_n)-h(\bar x))\|v\|$ for every $v\in\partial_L h(x_n)$, which is the distance form with $\operatorname{dist}(0,\emptyset)=+\infty$. The conclusion $h(x_n)<h(\bar x)+\eta$ is part of the paper's proof and makes the argument of $\varphi'$ lie in $(0,\eta)$, where $\varphi'$ is specified.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 6, Lemma 2.3 (first claim)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Lemma 2.3 (Boţ–Dao–Li, arXiv:2003.04124v2, p. 6), main claim: uniformized KL property along a
bounded sequence. If `(xₙ)` is bounded, `h` is proper, lower semicontinuous, constant on the set
`Ω` of cluster points and has the KL property at each point of `Ω`, and `Ω₀` is nonempty, then
there are `η > 0`, `φ ∈ Φ_η` and `n₀` such that for every `x̄ ∈ Ω₀` and `n ≥ n₀` with
`h(xₙ) > h(x̄)`: `h(xₙ) < h(x̄) + η` and `φ'(h(xₙ) - h(x̄)) ‖v‖ ≥ 1` for every `v ∈ ∂_L h(xₙ)`,
which is (9) with `dist(0, ∅) = +∞`. -/
theorem lemma_2_3 {N : ℕ} {h : EuclideanSpace ℝ (Fin N) → EReal}
    {x : ℕ → EuclideanSpace ℝ (Fin N)}
    (hbdd : Bornology.IsBounded (Set.range x))
    (hproper : IsProperFn h) (hlsc : LowerSemicontinuous h)
    (hconst : ∀ x₁ ∈ clusterSet x, ∀ x₂ ∈ clusterSet x, h x₁ = h x₂)
    (hKL : ∀ xbar ∈ clusterSet x, HasKLProperty h xbar)
    (hΩ₀ : (omega0 h x).Nonempty) :
    ∃ η : ℝ, 0 < η ∧ ∃ φ : ℝ → ℝ, IsDesingularizer η φ ∧ ∃ n₀ : ℕ,
      ∀ xbar ∈ omega0 h x, ∀ n, n₀ ≤ n → h xbar < h (x n) →
        h (x n) < h xbar + (η : EReal) ∧
        ∀ v ∈ LimitingSubdiff h (x n), 1 ≤ deriv φ (h (x n) - h xbar).toReal * ‖v‖ := by sorry

end FracPSG.Abstract
