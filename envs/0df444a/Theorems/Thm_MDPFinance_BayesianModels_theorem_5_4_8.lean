-- Prove2me | Theorems.Thm_MDPFinance_BayesianModels_theorem_5_4_8
-- name    : MDPFinance.BayesianModels.theorem_5_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:22.597381+00:00
-- url     : https://prove2.me/theorems/835ab703-cbca-4bf0-a1a9-154c54438f7d
-- title:
--   Theorem 5.4.8 — Bellman equation and optimal policy for the information-based model
-- statement:
--   **Theorem 5.4.8.** Suppose the information-based Markov Decision Model satisfies the
--   Structure Assumption of Theorem 2.3.8. Then:
--
--   a) The Bellman equation holds: $\hat J_0(x,i) = \int_\Theta g(x,\theta)\,\hat\mu(\mathrm
--   d\theta\mid i)$, and for $n \ge 1$, $\hat J_n(x,i) = \sup_{a \in D(x)} \big[\hat
--   r(x,i,a) + \beta \int \hat J_{n-1}\big(T^X(x,a,z),\hat\Phi(x,i,a,z)\big)\,Q^Z(\mathrm
--   dz\mid x,\theta,a)\,\hat\mu(\mathrm d\theta\mid i)\big]$ — i.e. the true (sup-over-policies)
--   value function $\hat J$ coincides with the operator recursion $T$-iterated from $\hat g$.
--
--   b) If $\hat f_n$ is a maximizer of $\hat J_{n-1}$ for $n=1,\dots,N$, then the policy
--   $\pi^* = (f_0^*,\dots,f_{N-1}^*)$ with $f_n^*(\tilde h_n) := \hat f_{N-n}(x_n,t_n(\tilde h_n))$
--   is optimal for the $N$-stage Bayesian Model.
--
--   This is Theorem 2.3.8 (this book's central finite-horizon result, formalized in chunk `02a`)
--   applied to the information-based model as a genuine instance: since that model is an ordinary
--   Markov Decision Model on $E_X \times I$, its Structure Assumption suffices for the same
--   Bellman-equation/optimal-Markov-policy conclusion, now translated back into an optimal policy for
--   the *original* (harder to analyze) Bayesian Model via the sufficient statistic.
--
--   **Formalization Note.** Earns the reduction explicitly rather than treating it as a
--   `kind: reference` to `02a`'s theorem, since the *instance* being verified (a stationary model
--   built from `InfoModel`'s data) is this chunk's own content.
--
--   **Moderation note.** Hypotheses carried from the book's standing assumptions: the chapter's Integrability Assumption for the Bayesian Model and the Integrability Assumption (AN) for the information-based model, which Theorem 2.3.8 needs; part a) for $n\le N$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 162-163, Theorem 5.4.8

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior
import Definitions.Def_MDPFinance_BayesianModels_SuffStat
import Definitions.Def_MDPFinance_BayesianModels_Policy
import Definitions.Def_MDPFinance_BayesianModels_Objective
import Definitions.Def_MDPFinance_BayesianModels_InfoModel
import Definitions.Def_MDPFinance_BayesianModels_Operators
import Definitions.Def_MDPFinance_BayesianModels_StructureAssumption

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

/-- Theorem 5.4.8 (Bäuerle–Rieder, p. 162-163, PDF 176). Suppose the information-based Markov
Decision Model satisfies the Structure Assumption of Theorem 2.3.8. a) Then the Bellman equation
holds, i.e. for `(x,i) ∈ E_X × I`: `Ĵ_0(x,i) = ∫ g(x,θ) μ̂(dθ|i)`, `Ĵ_n(x,i) = sup_{a ∈ D(x)}
[∫ r(x,θ,a) μ̂(dθ|i) + β ∫ Ĵ_{n-1}(T^X(x,a,z),Φ̂(x,i,a,z)) Q^Z(dz|x,θ,a) μ̂(dθ|i)]`. b) Let `f̂_n`
be a maximizer of `Ĵ_{n-1}` for `n = 1,\dots,N`. Then the policy `π^* := (f_0^*,\dots,f_{N-1}^*)`
is optimal for the `N`-stage Bayesian Model, where `f_n^*(h̃_n) := f̂_{N-n}(x_n,t_n(h̃_n))`.
Hypotheses carried from the book's standing assumptions: the chapter's Integrability Assumption
for the Bayesian Model (p. 151) and the Integrability Assumption (AN) for the information-based
model (Theorem 2.3.8's standing hypothesis, p. 18); part a) for `n ≤ N`. -/
theorem theorem_5_4_8 {EX Θ A Z I : Type*} [MeasurableSpace EX] [MeasurableSpace Θ]
    [MeasurableSpace A] [MeasurableSpace Z] [MeasurableSpace I] [Nonempty A] [Nonempty Z]
    (M : BayesModel EX Θ A Z) (Pf : M.Posterior) (S : SuffStat M Pf I)
    (Phihat : EX → I → A → Z → I) (hSeq : S.IsSequential Phihat) (Im : InfoModel M Pf S Phihat)
    (N : ℕ) (hInt : M.IntegrabilityAssumption N)
    (hAN : IntegrabilityOf (InfoD M) (fun ea => Im.Qhat ea)
      (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) (InfoG S) M.β N)
    (IMs : Set (EX × I → EReal)) (Δ : Set (EX × I → A))
    (hSAN : StructureAssumptionOf (InfoD M) (fun ea => Im.Qhat ea)
      (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) (InfoG S) M.β IMs Δ) :
    (Im.Jhat 0 = InfoG S) ∧
      (∀ n < N, Im.Jhat (n + 1) = Top (InfoD M) (fun ea => Im.Qhat ea)
        (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) M.β (Im.Jhat n)) ∧
      (∀ fhat : ℕ → EX × I → A,
        (∀ n, 1 ≤ n → n ≤ N → IsMaximizerOf (InfoD M) (fun ea => Im.Qhat ea)
          (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) M.β (Im.Jhat (n - 1)) (fhat n)) →
        M.IsPolicy N (fun n xs as zs => fhat (N - n) (xs n, S.t n xs as zs)) ∧
          ∀ x, M.JNpi (fun n xs as zs => fhat (N - n) (xs n, S.t n xs as zs)) N x =
            M.JN N x) := by sorry

end MDPFinance.BayesianModels
