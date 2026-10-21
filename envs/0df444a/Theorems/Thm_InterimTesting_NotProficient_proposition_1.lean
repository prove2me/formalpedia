-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_proposition_1
-- name    : InterimTesting.NotProficient.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:15.860764+00:00
-- url     : https://prove2.me/theorems/515034be-f989-4017-a5fc-8b013752b65b
-- title:
--   Proposition 1, pp. 16–17 (PDF 16–17) — from S0 = N, a free interim assessment is never strictly optimal if B = 0, and if B > 0 and (14) holds, it is strictly optimal exactly on two budget regions
-- statement:
--   Consider a school that starts the year not proficient ($S_0=N$), with a free interim assessment. For each assessment decision $z_I$ and budget $M\ge0$, let $\Pr^*_{z_I}(M)$ be the district's optimal probability that the school ends the year proficient, the supremum of $\Pr^*_{z_I}[S_2=P\mid S_0=N]$ over incentives $\pi\ge0$ with expected payment $\pi\Pr^*\le M$, under the teachers' optimal effort response. The district invests in the interim assessment only if $\Pr^*_0(M)<\Pr^*_1(M)$.
--
--   a) If $B=0$, then for every budget $M\ge0$ the two decisions give the same optimal probability, $\Pr^*_1(M)=\Pr^*_0(M)$, so the district does not invest, whatever the accuracy of the formative assessments.
--
--   b) If $B>0$ and (14) holds, then:
--
--   1. for $0\le M<M_L=\min\{\mathcal H_1(\mu),\mathcal H^I_1(\mu)\}$ and for $M\ge M_U=\frac{1+(1-\mu)B}{(1-\mu)A}+1$ the two decisions give the same optimal probability;
--   2. for every $M\ge0$, the interim assessment is strictly better if and only if
--   $$\mathcal H^I_1(\mu)\le M<\mathcal H_1(\mu)\qquad\text{or}\qquad\Big(\mu_0(B)<\mu\ \text{ and }\ \max\{\mathcal H^I_1(\mu),\mathcal H_1(\mu)\}\le M<\mathcal H_2(\mu)\Big).$$
--
--   The interim assessment helps a school that starts behind only at low and moderate budgets, and only when it starts with some chance of becoming proficient without extra effort.
--
--   **Formalization Note** "Optimal investment" is read as uniquely optimal, as the sentence after the proposition says ("the regions in which the interim assessment is uniquely optimal"). Two printed slips are corrected: $\mathcal H_2(\mu)$ is the product (A155), $\mu(A+B)(1+(1-\mu)B)\,\mathcal T_1(N,0,N)$, not the quotient printed in (17); and the second region requires $\mu_0(B)<\mu$ strictly, because at $\mu=\mu_0(B)$ the second steps of (A211) and (A212) coincide by (A214) and both decisions are optimal there. The page's $\mu_1$ phrasing is not needed in the equivalence: the first region is empty exactly when $\mu\ge\mu_1$ (Lemma A12). The remark "if $\mu_0(B)\le\mu_1$ … there is a region of $\mu$ for which both cases hold" is not formalized. Standing assumptions add $A>0$ and $0<\mu<1$ to Assumption 1 (at $\mu=0$ part b) fails). (14) is cross-multiplied and is not assumed in part a), where with $B=0$ it would be unsatisfiable.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), pp. 16–17 (PDF 16–17), Proposition 1, (15)–(18); expanded version p. A31 (PDF 57); proof pp. A31–A33 (PDF 57–59), (A155), (A207)–(A214)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Proposition 1, pp. 16–17 (expanded p. A31, proof p. A33): a school that starts not
proficient, free interim assessment. a) If `B = 0`, both assessment decisions give the same
optimal probability for every budget, so the district does not invest. b) If `B > 0` and (14)
holds, the decision is irrelevant below `M_L = min{ℋ1(μ), ℋ^I_1(μ)}` and from `M_U` on, and the
interim assessment is strictly better exactly when `ℋ^I_1(μ) ≤ M < ℋ1(μ)`, or when
`μ0(B) < μ` and `max{ℋ^I_1(μ), ℋ1(μ)} ≤ M < ℋ2(μ)`. -/
theorem proposition_1 (θ : Params) (hθ : θ.Standing) :
    (θ.B = 0 → ∀ M : ℝ, 0 ≤ M →
        optProb θ true .N M = optProb θ false .N M ∧ ¬ investsInterim θ .N M) ∧
      (0 < θ.B → Cond14 θ →
        (∀ M : ℝ, 0 ≤ M → M < ML θ → optProb θ true .N M = optProb θ false .N M) ∧
        (∀ M : ℝ, MU θ ≤ M → optProb θ true .N M = optProb θ false .N M) ∧
        (∀ M : ℝ, 0 ≤ M → (investsInterim θ .N M ↔
            (HI1 θ ≤ M ∧ M < H1 θ) ∨
            (mu0 θ < θ.μ ∧ max (HI1 θ) (H1 θ) ≤ M ∧ M < H2 θ)))) := by sorry

end InterimTesting.NotProficient
