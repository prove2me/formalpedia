-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace
-- name    : LanglandsTunnell.CubicInduction.localZeta31_identified_of_mem_gl3CyclicSubspace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2b4fca43-685c-5057-98e8-3b9ad22af5dd
-- title:
--   Identified local functional equation passes to the cyclic span
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb C^\times$, let $q$ be a nonzero prime of $\mathcal O_{\mathbb Q}$, let $W_3:\mathrm{GL}_3(\mathbb Q_q)\to\mathbb C$, and let $\mathrm{lam}\in\mathbb C$. The hypothesis `hId` asserts the following block for $W_3$, and the conclusion asserts it verbatim for $W$, for every $W$ in `gl3CyclicSubspace W₃`, the $\mathbb C$-span of the right translates $h\mapsto W_3(\cdot\,h)$: for every $b\in\mathbb N$ such that $2e(w/q)b+1\le \mathrm{conductorExponentAt}\,K\,w\,(\mu_w)$ for all $w$ in the fibre $\{w: w\cap\mathcal O_{\mathbb Q}=q\}$, every character $\eta$ of $\mathbb Q_q^\times$ admitting a conductor exponent $c_\eta\le b$, and every $\eta_{\mathbb A}$ on the ideles of $\mathbb Q$ that is trivial on principal ideles, continuous and unitary, has $q$-component $\eta$, and whose composite $\eta_K$ with the idelic norm of the base change $\mathbb Q\to K$ has the same three properties over $K$, and every $g\in\mathrm{GL}_3(\mathbb Q_q)$, there are $Q_1,Q_2\in\mathbb C[X]$ with $Q_2\ne 0$, $n\in\mathbb Z$ and $\sigma_0,\sigma_1\in\mathbb R$ such that: the integrand of `localZeta30` for $(W,\eta,g)$ against the pullback to the units of $dx/|x|$ for the self-dual Haar measure at $q$ is integrable for $\mathrm{Re}\,s>\sigma_0$, and there $Z_{3,0}(s)\,Q_2(Nq^{-s})=Q_1(Nq^{-s})\,Nq^{ns}$; the $(3,1)$ integrand for $\widetilde W=W(\,\mathrm{longWeyl}_3\,{}^t(\cdot)^{-1})$, $\eta^{-1}$ at `weylPrime3 * transposeInv3 g` is integrable for $\mathrm{Re}\,s>\sigma_1$; and for $\mathrm{Re}(1-s)>\sigma_1$, $$\widetilde Z_{3,1}(1-s)\,Q_2(Nq^{-s})=Q_1(Nq^{-s})\,Nq^{ns}\cdot\mathrm{lam}\cdot\prod_{w\mid q}(\eta_K\mu)_w(-1)\cdot\prod_{w\mid q}\bigl(\varepsilon(\tfrac12,(\eta_K\mu)_w)\,N(w)^{1/2-s}\bigr)^{a((\eta_K\mu)_w)+n(\psi_w)},$$ the products being finite products over the fibre and the exponent being `pinnedExp`, the conductor exponent plus the level of the standard local additive character.
--
--   This is the local linear-algebra step of Rankin–Selberg theory in the form used here: the $(3,1)$ local zeta integrals are linear in the Whittaker function and right translation only moves the argument $g$, so a functional equation with the identified constant $\lambda\prod_{w\mid q}(\eta_K\mu)_w(-1)\prod_{w\mid q}(\varepsilon\,N(w)^{1/2-s})^{\mathrm{pinnedExp}}$ for one function propagates, with the same constant, to its whole cyclic span. It is invoked in the construction of the cubic-induction local data at the deep places, both at a single place and over the bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_localZeta31_identified_of_mem_gl3CyclicSubspace.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.TateLocal

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.localZeta31_identified_of_mem_gl3CyclicSubspace
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (q : HeightOneSpectrum (𝓞 ℚ))
    (W₃ : LocalGL3 q → ℂ) (lam : ℂ)
    (hId :
      ∀ b : ℕ,
        (∀ w ∈ primeFibre ℚ K q,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : (q.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ q η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA q = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 q,
              letI := LanglandsTunnell.TateLocal.localBorel ℚ q
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove q
                  (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                  W₃ η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 q
                      (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                      W₃ η s g *
                    Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove q
                  (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                  (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) (dualWhittakerFn3 W₃) η⁻¹
                  (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 q
                      (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                      (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) W₃ η (1 - s) g *
                    Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lam *
                      (∏ᶠ w ∈ primeFibre ℚ K q,
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ primeFibre ℚ K q,
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))
    (W : LocalGL3 q → ℂ) (hW : W ∈ gl3CyclicSubspace W₃) :
    ∀ b : ℕ,
      (∀ w ∈ primeFibre ℚ K q,
        2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
          LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
      ∀ (η : (q.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ q η cη → cη ≤ b →
        ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
          NumberField.TateGlobal.localChar ηA q = η →
          LanglandsTunnell.Converse.IsAdmissibleTwist K
            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
          ∀ g : LocalGL3 q,
            letI := LanglandsTunnell.TateLocal.localBorel ℚ q
            ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
              IsLocalZeta30ConvergentAbove q
                (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                W η g σ₀ ∧
              (∀ s : ℂ, σ₀ < s.re →
                localZeta30 q
                    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                    W η s g *
                  Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
              IsLocalZeta31ConvergentAbove q
                (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) (dualWhittakerFn3 W) η⁻¹
                (weylPrime3 * transposeInv3 g) σ₁ ∧
              (∀ s : ℂ, σ₁ < (1 - s).re →
                localZetaDual31 q
                    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q)))
                    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ q) W η (1 - s) g *
                  Q₂.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) =
                Q₁.eval ((Ideal.absNorm q.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm q.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                  (lam *
                    (∏ᶠ w ∈ primeFibre ℚ K q,
                      ((NumberField.TateGlobal.localChar
                        (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                    (∏ᶠ w ∈ primeFibre ℚ K q,
                      (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                          (NumberField.TateGlobal.localChar
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                        (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                          (LanglandsTunnell.Converse.pinnedExp K
                            (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))) := by sorry
