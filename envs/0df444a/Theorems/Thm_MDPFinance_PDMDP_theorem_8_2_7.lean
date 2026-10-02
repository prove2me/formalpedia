-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_theorem_8_2_7
-- name    : MDPFinance.PDMDP.theorem_8_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:13.8354+00:00
-- url     : https://prove2.me/theorems/f9b6a82f-b734-4012-aef3-587a238fa44a
-- title:
--   Theorem 8.2.7 — existence of an optimal nonrelaxed policy
-- statement:
--   This theorem upgrades Theorem 8.2.6's relaxed optimal policy to a genuine, nonrelaxed ($U$-valued) one, under either of two extra conditions: the flow is uncontrolled (so a pointwise maximizer over $U$ already achieves the relaxed supremum), or $U$ is convex, $\mu(x,u)$ is linear in $u$, and $u \mapsto r(x,u)+\lambda\int J^{rel}_\infty\,dQ(\cdot\mid x,u)$ is concave (so the relaxed optimum's barycenter is itself optimal, by Jensen's inequality applied to the concave objective). Either way, the conclusion identifies the three value functions $J_\infty$ (nonrelaxed embedded), $J^{rel}_\infty$ (relaxed embedded), and confirms $J_\infty$ is itself a fixed point of the nonrelaxed operator $T$ — the book's own remark "$V_\infty=J_\infty=J^{rel}_\infty$" is rendered as this identification between the two embedded-model value functions, per this chunk's operational reading of $V_\infty$ (see `theorem_8_2_1`).
--
--   **Formalization Note.** $\mu$ and the vector-space structure on $U$/$E$ needed for "convex"/"linear"/"concave" to typecheck are hypothesis-only parameters of this one theorem (not stored on `PDMDPModel`), since no other item in this chunk needs them.
--
--   **Moderation note.** The draft's Theorem 8.2.7 named a *free* function `μ` unrelated to the model's drift, and its "`U` is a compact subset of a vector space" branch quantified over a vector space structure on `U` with no link to the drift or reward, so the concavity condition was vacuous or unrelated. Now the alternative is: either the flow is uncontrolled (`μ(x,u)` independent of `u`), or `U` embeds by a continuous injection `ι` into a real normed space `V` with `ι(U)` convex, the drift is affine in the control through a linear map `L_x : V → E` (`μ(x,u) = m(x) + L_x ι(u)`) and the reward is concave in the control in the sense `r(x, ·)∘ι` concave on `ι(U)` (`[-∞,∞]`-valued inequality), and the conclusion is `J_∞ = J^r_∞` (ordinary policies suffice) with an ordinary measurable maximizer.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 254-255, PDF 265-266, Theorem 8.2.7

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Bounding
import Definitions.Def_MDPFinance_PDMDP_Relaxed
import Definitions.Def_MDPFinance_PDMDP_Process

open MeasureTheory ProbabilityTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U]
  [TopologicalSpace.MetrizableSpace U] [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.2.7 (Bäuerle–Rieder, p. 253-254, PDF 264-265). Under the hypotheses of Theorem
8.2.6, if the flow `φ_t^α(x)` is independent of `α` (uncontrolled flow), or if `U` is convex,
`μ(x,u)` is linear in `u` and `u ↦ r(x,u) + λ ∫ J^{rel}_∞(z) Q(dz|x,u)` is concave on `U`, then
there exists an optimal **nonrelaxed** stationary Markov policy `π^*_t = f(Z_n)(t-T_n)`,
`f : E → A` measurable, and `V_∞ = J_∞ = J^{rel}_∞`; in particular `V_∞` is a fixed point of
`T`. "`U` convex, `μ` linear in `u`" is stated through an injective continuous embedding
`Uemb : U → V` of the control space into a real normed space `V` (the book's `U` is a convex
Borel subset of such a space): `Uemb '' U` convex, `μ(x,·) = L_x ∘ Uemb` with `L_x` linear, and
concavity along convex combinations taken in `V`. `V_∞` is read as `J_∞` of the nonrelaxed
embedded model (`JinfSup`), per Theorem 8.2.1. -/
theorem theorem_8_2_7 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (EmbR : EmbeddedKernelRelaxed Mk) (b : E → ℝ)
    (hb_cont : Continuous b) (cr cQ cφ : ℝ) (hbound : IsUpperBoundingFunctionPDMDP Mk b cr cQ cφ)
    (hαb : cQ * cφ < 1) (hcc : ContinuityCompactnessAssumptions Mk b)
    (Uemb : U → V) (hUemb_cont : Continuous Uemb) (hUemb_inj : Function.Injective Uemb)
    (hcase :
      (∀ t x (α α' : ℝ → U), Measurable α → Measurable α' → Mk.φ t α x = Mk.φ t α' x) ∨
        (Convex ℝ (Set.range Uemb) ∧
          (∀ x, ∃ Lx : V →ₗ[ℝ] E, ∀ u, Mk.μ (x, u) = Lx (Uemb u)) ∧
          ∀ x (u v w : U) (a c : ℝ), 0 ≤ a → 0 ≤ c → a + c = 1 →
            Uemb w = a • Uemb u + c • Uemb v →
            (a : EReal) * (((Mk.r (x, u) : ℝ) : EReal) +
                (Mk.lam : EReal) * erealIntegral (Mk.Q (x, u)) (JrelInfSup Mk EmbR)) +
              (c : EReal) * (((Mk.r (x, v) : ℝ) : EReal) +
                (Mk.lam : EReal) * erealIntegral (Mk.Q (x, v)) (JrelInfSup Mk EmbR)) ≤
            ((Mk.r (x, w) : ℝ) : EReal) +
              (Mk.lam : EReal) * erealIntegral (Mk.Q (x, w)) (JrelInfSup Mk EmbR))) :
    ∃ f : E → ControlFn U, Measurable f ∧
      (∀ x, JinfEmbed Mk Emb (fun _ => f) x = JinfSup Mk Emb x) ∧
      (∀ x, JinfSup Mk Emb x = JrelInfSup Mk EmbR x) ∧
      ∀ x, JinfSup Mk Emb x = TEmbed Mk Emb (JinfSup Mk Emb) x := by sorry

end MDPFinance.PDMDP
