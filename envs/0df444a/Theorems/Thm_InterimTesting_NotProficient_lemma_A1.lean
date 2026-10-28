-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A1
-- name    : InterimTesting.NotProficient.lemma_A1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:34.855122+00:00
-- url     : https://prove2.me/theorems/9a0b74aa-5afd-4ba6-8145-6dc1ed3d7549
-- title:
--   Lemma A1, p. A3 (PDF 29) — law of the midyear observation (A2), Bayes posterior (A4), and conditional end-of-year proficiency (A3)
-- statement:
--   Fix the assessment decision $z_I$, the starting state $S_0$ and a first-period effort $e_0\in[0,1]$, and write $m=m(e_0,S_0)$ ($=Ae_0+B$ if $S_0=P$, $\mu(Ae_0+B)$ if $S_0=N$). Let $(a,b)=(\phi_{P|P},\phi_{P|N})$ under the formative assessment and $(a,b)=(1,0)$ under the interim assessment. Then
--   $$\Pr[X_1=P]=a\,m+b\,(1-m),$$
--   $$\Pr[\beta_1=P\mid X_1=P]=\frac{a\,m}{a\,m+b(1-m)},\qquad \Pr[\beta_1=P\mid X_1=N]=\frac{(1-a)\,m}{(1-a)\,m+(1-b)(1-m)},$$
--   and, for every observation $x$ of positive probability and every second-period effort $e_1$,
--   $$\Pr[\beta_2=P\mid X_1=x]=(Ae_1+B)\,p_x+\mu(Ae_1+B)\,(1-p_x),\qquad p_x=\Pr[\beta_1=P\mid X_1=x].$$
--
--   These identities connect the primitive probabilities of the model to the posterior form in which the teachers' second-period problem is written.
--
--   **Formalization Note** The last identity is stated as `(joint P x · toP P e1 + joint N x · toP N e1) / obsProb x = finalP (post x) e1` for `obsProb x ≠ 0`. Standing assumptions $A>0$, $0<\mu<1$ are carried by every statement of the mission.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A3 (PDF 29), Lemma A1, (A1)–(A4)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A1, p. A3: the law of the midyear observation (A2), the posterior (A4), and the
conditional probability of ending proficient (A3). Here `(a, b) = acc θ zI` is
`(ϕ_{P|P}, ϕ_{P|N})` without and `(1, 0)` with the interim assessment, and `m = m(e0, S0)`. -/
theorem lemma_A1 (θ : Params) (hθ : θ.Standing) (zI : Bool) (S0 : Prof) (e0 : ℝ)
    (he0 : e0 ∈ Set.Icc (0 : ℝ) 1) :
    obsProb θ zI S0 e0 .P =
        (acc θ zI).1 * toP θ S0 e0 + (acc θ zI).2 * (1 - toP θ S0 e0) ∧
      post θ zI S0 e0 .P = (acc θ zI).1 * toP θ S0 e0 /
        ((acc θ zI).1 * toP θ S0 e0 + (acc θ zI).2 * (1 - toP θ S0 e0)) ∧
      post θ zI S0 e0 .N = (1 - (acc θ zI).1) * toP θ S0 e0 /
        ((1 - (acc θ zI).1) * toP θ S0 e0 + (1 - (acc θ zI).2) * (1 - toP θ S0 e0)) ∧
      ∀ (x : Prof) (e1 : ℝ), obsProb θ zI S0 e0 x ≠ 0 →
        (joint θ zI S0 e0 .P x * toP θ .P e1 + joint θ zI S0 e0 .N x * toP θ .N e1) /
            obsProb θ zI S0 e0 x = finalP θ (post θ zI S0 e0 x) e1 := by sorry

end InterimTesting.NotProficient
