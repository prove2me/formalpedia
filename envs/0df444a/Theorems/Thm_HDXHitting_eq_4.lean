-- Prove2me | Theorems.Thm_HDXHitting_eq_4
-- name    : HDXHitting.eq_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T18:02:12.859159+00:00
-- url     : https://prove2.me/theorems/3b67ae91-3801-4bff-973c-9a4f75d7d9ba
-- title:
--   Eq. (4) — $\frac{d}{d\mu}c_d(\mu)\le d(\mu+\lambda)(\mu+d\lambda)^{d-2}$ (one-step form)
-- statement:
--   Let $p$ be the top distribution of a $d$-dimensional $\lambda$-one-sided HDX with $d\ge2$ and $\lambda\ge0$, and assume the induction hypothesis: every $(d-1)$-dimensional $\lambda$-one-sided HDX on the same vertex set satisfies $\mathbb E_{\tau\sim\pi_{d-1}}[\prod_{v\in\tau}f(v)]\le\mu(\mu+(d-1)\lambda)^{d-2}$ for every $f:V\to[0,1]$ of mean $\mu$. Then for every $\mu\in(0,1)$ there is $s_0>0$ such that for all $s\in(0,s_0)$
--   $$
--   c_d(\mu)\le c_d(\mu-s)+s\cdot d(\mu+\lambda)(\mu+d\lambda)^{d-2} .
--   $$
--   This is the derivative bound (4), $\frac{d}{d\mu}c_d(\mu)\le d(\mu+\lambda)(\mu+d\lambda)^{d-2}$, in the form the page derives it (with $s=\epsilon\pi(v)$); integrating from $c_d(0)=0$ gives $c_d(\mu)\le\mu(\mu+d\lambda)^{d-1}$.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: second eigenvalue of every link graph at most λ → IsOneSidedHDX: the published Rayleigh-form HDXConc.SecondEigLE on unnormalized link weights for every τ with |τ| + 2 ≤ d; reason: Courant–Fischer for the self-adjoint walk; scale invariance
--   - reading: d/dµ c_d(µ) ≤ d(µ + λ)(µ + dλ)^{d−2} → for each µ ∈ (0, 1), c_d(µ) ≤ c_d(µ − s) + s·d(µ + λ)(µ + dλ)^{d−2} for all small s > 0; reason: c_d is only Lipschitz, so the derivative need not exist; this is the inequality the page derives, and it bounds the derivative wherever it exists
--   - reading: the induction hypothesis on d → an explicit hypothesis: the one-sided bound for every (d − 1)-dimensional λ-one-sided HDX on V; reason: an inductive step stated as an implication
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Eq. (4), proof of Lemma 3.2, p.16

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_cMax

namespace HDXHitting

/-- Eq. (4) (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, p.16), as the one-step inequality the page derives:
on a `d`-dimensional `λ`-one-sided HDX (`d ≥ 2`, `λ ≥ 0`), assuming the induction hypothesis
(the one-sided bound of Lemma 3.2 for every `(d − 1)`-dimensional `λ`-one-sided HDX on the same
vertex type), for every `µ ∈ (0, 1)` there is `s₀ > 0` with
`c_d(µ) ≤ c_d(µ − s) + s · d(µ + λ)(µ + dλ)^{d−2}` for all `s ∈ (0, s₀)`; i.e. the (left)
derivative bound `d/dµ c_d(µ) ≤ d(µ + λ)(µ + dλ)^{d−2}`.

**Formalization Note** `c_d` is only Lipschitz, so its derivative need not exist everywhere;
the statement is the difference inequality from which the page reads off (4) (with
`s = ε π(v)`). -/
theorem eq_4 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 2 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsOneSidedHDX d p lam)
    (ih : ∀ p' : Finset V → ℝ, IsTopDist (d - 1) p' → IsOneSidedHDX (d - 1) p' lam →
      ∀ f : V → ℝ, (∀ v, 0 ≤ f v ∧ f v ≤ 1) →
        hit p' f ≤ mean (d - 1) p' f * (mean (d - 1) p' f + ((d - 1 : ℕ) : ℝ) * lam) ^ (d - 2)) :
    ∀ μ : ℝ, 0 < μ → μ < 1 → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      cMax d p μ ≤ cMax d p (μ - s) + s * ((d : ℝ) * (μ + lam) * (μ + d * lam) ^ (d - 2)) := by sorry

end HDXHitting
