-- Prove2me | Theorems.Thm_FracPSG_Abstract_lemma_2_3_exponent
-- name    : FracPSG.Abstract.lemma_2_3_exponent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:48.371482+00:00
-- url     : https://prove2.me/theorems/0c07daca-058c-4a6f-8fc8-4bb50fcd1c35
-- title:
--   Lemma 2.3 (Moreover) — uniformized KL with a power desingularizer
-- statement:
--   Under the hypotheses of Lemma 2.3 (a bounded sequence $(x_n)$ in $\mathcal H$, its cluster set $\Omega$, a proper lower semicontinuous $h$ constant on $\Omega$ with the KL property on $\Omega$, and $\Omega_0\ne\emptyset$), suppose moreover that $h$ has the KL property at every point of $\Omega$ with one exponent $a\in[0,1)$. Then the uniformized inequality of Lemma 2.3 holds with $\varphi(s)=\gamma s^{1-a}$ for some $\gamma>0$: there are $\eta>0$, $\gamma>0$ and $n_0$ such that $\varphi\in\Phi_\eta$ and, for every $\bar x\in\Omega_0$ and $n\ge n_0$ with $h(x_n)>h(\bar x)$, $h(x_n)<h(\bar x)+\eta$ and
--   $$\gamma(1-a)\big(h(x_n)-h(\bar x)\big)^{-a}\operatorname{dist}\big(0,\partial_L h(x_n)\big)\ge1 .$$
--
--   The power form of $\varphi$ is what converts the finite-length argument into explicit linear rates when $a\le\tfrac12$ (Theorem 5.2(iv)).
--
--   **Formalization Note** The exponent is named $a$ because the paper's $\alpha$ also denotes the sequence $(\alpha_n)$. $\varphi'$ is Lean's `deriv` of $s\mapsto\gamma s^{1-a}$ (real power), which equals $\gamma(1-a)s^{-a}$ for $s>0$. Distances are encoded as in Lemma 2.3.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 6, Lemma 2.3 ("Moreover" claim)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Lemma 2.3 (Boţ–Dao–Li, arXiv:2003.04124v2, p. 6), "Moreover" claim: if in addition `h` has the
KL property at every point of `Ω` with one exponent `a`, the uniformized function can be chosen as
`φ(s) = γ s^{1-a}` with `γ > 0`. -/
theorem lemma_2_3_exponent {N : ℕ} {h : EuclideanSpace ℝ (Fin N) → EReal}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {a : ℝ}
    (hbdd : Bornology.IsBounded (Set.range x))
    (hproper : IsProperFn h) (hlsc : LowerSemicontinuous h)
    (hconst : ∀ x₁ ∈ clusterSet x, ∀ x₂ ∈ clusterSet x, h x₁ = h x₂)
    (hKL : ∀ xbar ∈ clusterSet x, HasKLProperty h xbar)
    (hKLexp : ∀ xbar ∈ clusterSet x, HasKLPropertyExp h xbar a)
    (hΩ₀ : (omega0 h x).Nonempty) :
    ∃ η : ℝ, 0 < η ∧ ∃ γ : ℝ, 0 < γ ∧
      IsDesingularizer η (fun s => γ * s ^ (1 - a)) ∧ ∃ n₀ : ℕ,
      ∀ xbar ∈ omega0 h x, ∀ n, n₀ ≤ n → h xbar < h (x n) →
        h (x n) < h xbar + (η : EReal) ∧
        ∀ v ∈ LimitingSubdiff h (x n),
          1 ≤ deriv (fun s => γ * s ^ (1 - a)) (h (x n) - h xbar).toReal * ‖v‖ := by sorry

end FracPSG.Abstract
