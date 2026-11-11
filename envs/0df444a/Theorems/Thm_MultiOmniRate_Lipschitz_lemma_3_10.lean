-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_10
-- name    : MultiOmniRate.Lipschitz.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:16.584727+00:00
-- url     : https://prove2.me/theorems/3cf56921-b172-4fff-8152-5364fefe953a
-- title:
--   Lemma 3.10 — concave, bounded, $\ell_1$-Lipschitz functions on the $d$-simplex have uniform $\rho$-covers with $\log(2M)\le C_d\rho^{-d/2}$
-- statement:
--   Let $d\ge1$ and let $\Sigma_d=\{x\in[0,1]^d:\sum_ix_i\le1\}$ be the standard $d$-dimensional simplex. For every bound $B\ge0$ and Lipschitz constant $\Lambda\ge0$ there is $C_d>0$, depending only on $d$, $B$ and $\Lambda$, such that every class $\mathcal F$ of functions that are concave on $\Sigma_d$, satisfy $|f|\le B$ on $\Sigma_d$ and $|f(x)-f(y)|\le\Lambda\|x-y\|_1$ for $x,y\in\Sigma_d$ has, for every $0<\rho\le1$, a uniform $\rho$-cover (on $\Sigma_d$) of some size $M$ with
--   $$\log(2M)\le C_d\,\rho^{-d/2}.$$
--
--   This is Bronshtein's entropy bound (in the form of Guntuboyina and Sen) transferred from the cube to the simplex; it supplies the covers of Bayes risks.
--
--   Differences from the source:
--   - encoding: "the standard $d$-dimensional simplex"; a cover of the class → `cornerSimplex d` $=\Sigma_d$ (App. A.2.1's coordinates); functions $\mathbb R^d\to\mathbb R$ with every property on $\Sigma_d$, cover elements arbitrary functions compared on $\Sigma_d$; reason: the paper's own coordinates in the proof; Definition 3.9 does not require cover elements in the class
--   - encoding: "uniformly bounded absolute values and a common Lipschitz constant" → explicit $B\ge0$ and $\Lambda\ge0$ quantified before $C$; reason: "$C_d$ depends only on $d$, the common bound and the common Lipschitz constant"
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 29, Lemma 3.10 (proof: p. 55, App. A.2.1)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_10 :
    ∀ (d : ℕ), 1 ≤ d → ∀ (Bd Λ : ℝ), 0 ≤ Bd → 0 ≤ Λ → ∃ C : ℝ, 0 < C ∧
      ∀ (F : Set ((Fin d → ℝ) → ℝ)),
        (∀ f ∈ F, ConcaveOn ℝ (cornerSimplex d) f ∧ (∀ x ∈ cornerSimplex d, |f x| ≤ Bd) ∧
          ∀ x ∈ cornerSimplex d, ∀ y ∈ cornerSimplex d, |f x - f y| ≤ Λ * ∑ i, |x i - y i|) →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
          ∃ B : Finset ((Fin d → ℝ) → ℝ),
            (∀ f ∈ F, ∃ b ∈ B, ∀ x ∈ cornerSimplex d, |f x - b x| ≤ ρ) ∧
            Real.log (2 * (B.card : ℝ)) ≤ C * ρ ^ (-(d : ℝ) / 2) := by sorry

end MultiOmniRate.Lipschitz
