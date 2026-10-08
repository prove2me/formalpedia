-- Prove2me | Theorems.Thm_MDPFinance_Semicontinuous_weakly_continuous_kernel_iff
-- name    : MDPFinance.Semicontinuous.weakly_continuous_kernel_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:26:46.465583+00:00
-- url     : https://prove2.me/theorems/1ec1e930-f6a5-439b-91ec-4663fbe01e55
-- title:
--   Lemma 2.4.7 — weakly continuous kernels
-- statement:
--   Let $b$ be a continuous upper bounding function, and let $Q$ be a stochastic kernel on $E$
--   given $E \times A$. The following are equivalent: (i) $(x,a) \mapsto \int v(x')\, Q(dx'
--   \mid x,a)$ is upper semicontinuous for every upper semicontinuous $v \in \mathrm{IB}_b^+$;
--   (ii) $(x,a) \mapsto \int b(x')\, Q(dx' \mid x,a)$ is continuous, and $(x,a) \mapsto \int v(x')\,
--   Q(dx' \mid x,a)$ is continuous and bounded for every continuous and bounded $v$ on $E$. A
--   kernel satisfying (ii) is called **weakly continuous**.
--
--   Condition (ii) is the one actually checked in applications (it only involves continuous
--   bounded test functions, not the whole class $\mathrm{IB}_b^+$), which is why the lemma is
--   stated as an equivalence: it converts hypothesis (ii) of Theorem 2.4.6 into a criterion on
--   $Q_n$ alone, reusable across every later application of that theorem in the book.
--
--   **Formalization Note.** $b$'s role as an upper bounding function of an ambient model $M$ is
--   carried only as standing context, matching the book's own section-wide running assumption; the
--   equivalence itself is about an arbitrary kernel $Q$, not necessarily one of $M$'s own $Q_n$.
--
--   **Formalization Note (moderation).** The kernel $Q$ is assumed to integrate $b$ finitely
--   (`hQb`, automatic for the model's own $Q_n$ by Definition 2.4.1(iii)), so that $\int b\,dQ$ in
--   (ii) is the genuine integral rather than the Bochner integral's default value $0$. Borel-space
--   assumptions on $E$, $A$ as in the rest of Section 2.4.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 31, Lemma 2.4.7

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous

/-- Lemma 2.4.7 (Bäuerle–Rieder, p. 31, PDF 46): let `b` be a continuous upper bounding
function. Then the following are equivalent, for an arbitrary stochastic kernel `Q` on `E`
given `E × A`: (i) `(x,a) ↦ ∫ v(x') Q(dx'|x,a)` is upper semicontinuous for all upper
semicontinuous `v ∈ IB_b^+`; (ii) `(x,a) ↦ ∫ b(x') Q(dx'|x,a)` is continuous, and
`(x,a) ↦ ∫ v(x') Q(dx'|x,a)` is continuous and bounded for all continuous and bounded `v` on
`E`. A kernel satisfying (ii) is called weakly continuous. `b`'s role as an upper bounding
function of the ambient model `M` is carried only as standing context (the section's own
running hypothesis); the equivalence itself concerns an arbitrary stochastic kernel `Q`, not necessarily
one of `M`'s own `Q_n`, exactly as the book states it, under which `b` is integrable (`hQb`, as it is
under each `Q_n` by Definition 2.4.1(iii)), so that `∫ b dQ` in (ii) is the genuine integral. `E` and `A` are Borel spaces (Borel subsets of Polish spaces with their
relative topologies: separable metrizable, with standard Borel σ-algebras), the standing assumption
of Section 2.4. -/
theorem weakly_continuous_kernel_iff {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (hb_cont : Continuous b)
    (Q : Kernel (E × A) E) [∀ p, IsProbabilityMeasure (Q p)]
    (hQb : ∀ p, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) < ⊤) :
    (∀ v : E → EReal, v ∈ IBbPlus b → UpperSemicontinuous v →
        UpperSemicontinuous (fun p : E × A => erealIntegral (Q p) v))
    ↔
    (Continuous (fun p : E × A => ∫ x', b x' ∂(Q p)) ∧
     ∀ v : E → ℝ, Continuous v → (∃ c, ∀ x, |v x| ≤ c) →
       Continuous (fun p : E × A => ∫ x', v x' ∂(Q p)) ∧
       ∃ c, ∀ p, |∫ x', v x' ∂(Q p)| ≤ c) := by sorry

end MDPFinance.Semicontinuous
