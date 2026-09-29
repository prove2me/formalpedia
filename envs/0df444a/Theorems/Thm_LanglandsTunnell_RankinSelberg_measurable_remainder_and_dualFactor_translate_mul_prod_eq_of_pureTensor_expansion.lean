-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
-- name    : LanglandsTunnell.RankinSelberg.measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/c183852b-ffff-51c0-abd4-2a3d34897751
-- title:
--   Measurability and isolation identity for pure-tensor remainders
-- statement:
--   Fix a number field $K$ with $\mathcal O_K$ integral over $\mathcal O_{\mathbb Q}$, a datum `pins : CarrierPins ℚ`, an additive character $\psi$ of the adeles of $\mathbb Q$ whose inverse is the standard character `psiQ`, a character $\mu$ of the idele units of $K$, and a cubic induction form $F$ of type `CubicInductionForm K pins ψ μ`. Let $S_Q$ be a finite set of finite places of $\mathbb Q$, let $h_\mu$ lie in `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean component map on $\mathrm{GL}_2$ of the adeles), let $m\in\mathbb N$, and let $w_{p,\alpha}:\mathrm{GL}_2(\mathbb Q_p)\to\mathbb C$ for $p\in S_Q$, $\alpha\in\mathrm{Fin}\,m$ satisfy the $\psi_p$-Whittaker law $w_{p,\alpha}(u(x)g)=\psi_{\mathbb Q,p}(x)w_{p,\alpha}(g)$ for the upper unipotent $u(x)$. Let $W^{\mathrm{rem}}_\alpha$ on adelic $\mathrm{GL}_2$ be right invariant under the local embedding of $\mathrm{GL}_2(\mathbb Q_p)$ for $p\in S_Q$ and satisfy $W^{\mathrm{rem}}_\alpha(u(t)g)=\psi_{\mathbb Q}(t)W^{\mathrm{rem}}_\alpha(g)$ for adeles $t$ with vanishing archimedean part whose unipotent is trivial at every $p\in S_Q$; both the slots $w_{p,\alpha}\circ\mathrm{loc}_p$ and the $W^{\mathrm{rem}}_\alpha$ are assumed measurable on the finite-adelic subgroup. Let $W_f,W_f^\vee$ be complex functions on that subgroup, let $w_0\in\mathrm{GL}_2(\mathbb Q)$ have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and assume $W_f^\vee(g_f)=\|\det g_f\|\,W_f\bigl(\mathrm{finFactor}(w_0\,{}^t g_f^{-1})\bigr)$, where $\|\cdot\|$ is the idele norm and `finFactor` removes the archimedean part, together with the pure-tensor expansion $W_f(\mathrm{finFactor}\,g)=\sum_\alpha\bigl(\prod_{p\in S_Q}w_{p,\alpha}(g_p)\bigr)W^{\mathrm{rem}}_\alpha(g)$. Let $R_\alpha$ on adelic $\mathrm{GL}_2$ be right invariant under the local embeddings at $p\in S_Q$ and satisfy the dual expansion $W_f^\vee(\mathrm{finFactor}(g)h_\mu)=\sum_\alpha\bigl(\prod_{p\in S_Q}|\det g_p|_p\,w_{p,\alpha}(w_{0,p}\,{}^tg_p^{-1})\bigr)R_\alpha(g)$, the modulus being the Haar modulus of the completion. Finally fix points $y^{(i)}_p\in\mathrm{GL}_2(\mathbb Q_p)$, elements $k_{0,p}\in\mathrm{GL}_3(\mathbb Q_p)$ and subgroups $U_p\le\mathrm{GL}_2(\mathbb Q_p)$ such that left multiplication by $U_p$ does not change $w_{p,\beta}(w_{0,p}\,{}^t(y^{(i)}_p)^{-1})$, such that $F.\mathrm{whittakerLoc}_p(w_3\,{}^t\iota(u)^{-1}k_{0,p})=F.\mathrm{whittakerLoc}_p(w_3k_{0,p})$ for $u\in U_p$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$ and $\iota$ the embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$, such that $F.\mathrm{whittakerLoc}_p(w_3k_{0,p})\neq0$, and such that the $m\times m$ matrix $M_{i\beta}=\prod_{p\in S_Q}w_{p,\beta}(w_{0,p}\,{}^t(y^{(i)}_p)^{-1})$ has nonzero determinant. The conclusion is fivefold: (1) $W_f^\vee$ is measurable; (2) for each $n$ in the unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) of the finite-adelic subgroup there is $\theta$ with $\|\theta\|=1$ and $W_f^\vee(ng)=\theta W_f^\vee(g)$ for all $g$; (3) each $R_\alpha$ is measurable on the finite-adelic subgroup; (4) $\|R_\alpha(ng)\|=\|R_\alpha(g)\|$ for such $n$; and (5) the isolation identity: whenever $g,\hat y$ lie in the finite-adelic subgroup, $i\in\mathrm{Fin}\,m$, the local component of $g$ at each $p\in S_Q$ factors as $n\,u$ with $n$ in the range of `unipotentGL2Hom` over $\mathbb Q_p$ and $u\in U_p$, the local component of $\hat y$ at $p\in S_Q$ equals $y^{(i)}_p$, and $\hat y$ is trivial at every finite place outside $S_Q$, then $$W_f^\vee(g\hat y h_\mu)\prod_{p\in S_Q}F.\mathrm{whittakerLoc}_p\bigl(w_3\,{}^t\iota((g\hat y)_p)^{-1}({}^t\iota(y^{(i)}_p)^{-1})^{-1}k_{0,p}\bigr)=\Bigl(\prod_{p\in S_Q}F.\mathrm{whittakerLoc}_p(w_3k_{0,p})\,|\det g_p|_p\,|\det y^{(i)}_p|_p\Bigr)\sum_\beta\Bigl(\prod_{p\in S_Q}w_{p,\beta}(w_{0,p}\,{}^t(y^{(i)}_p)^{-1})\Bigr)R_\beta(g).$$
--
--   This is the bookkeeping step accompanying a finite pure-tensor decomposition of the finite-adelic Whittaker factor over a finite set of primes: it records measurability and unitary unipotent equivariance of the dual function and of the remainder coefficients, and the identity that isolates the remainders $R_\beta$ against the local Whittaker values of the cubic induction form on the cut-off region. It is used in [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_cutoff_remainder_mul_finprod_away`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_cutoff_remainder_mul_finprod_away), within the Rankin–Selberg convergence analysis for the converse theorem in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_LambdaSquared

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open LanglandsTunnell.TateLocal UnramifiedWhittaker in

theorem LanglandsTunnell.RankinSelberg.measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ μ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hμf : finiteAdelicGL2Subgroup ℚ)
    (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)
    (Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hWinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wrem α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = Wrem α g)
    (_hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wrem α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * Wrem α g)
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (Wf Wfd : finiteAdelicGL2Subgroup ℚ → ℂ)
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
    (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hRinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R α g)
    (_hRexp : ∀ g : finiteAdelicGL2Subgroup ℚ, Wfd (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) =
      ∑ α : Fin m, (∏ p : ↥SQ,
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (yy : Fin m → ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
    (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))
    (hU1 : (∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
        w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (u * yy i p)) =
          w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))))
    (hU2 : (∀ (p : ↥SQ), ∀ u ∈ U p,
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
          F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)))
    (hc₀ : (∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0))
    (hM : ((Matrix.of fun i j : Fin m => ∏ p : ↥SQ,
        w p j (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))).det ≠ 0)) :
    Measurable Wfd ∧
    (∀ n : ↥RSCarrier.finUnipotent, ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ g : finiteAdelicGL2Subgroup ℚ,
      Wfd ((n : finiteAdelicGL2Subgroup ℚ) * g) = θ * Wfd g) ∧
    (∀ α : Fin m, Measurable fun g : finiteAdelicGL2Subgroup ℚ => R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
    (∀ (α : Fin m) (n : ↥RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖R α (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖R α (g : AdelicGL2 (𝓞 ℚ) ℚ)‖) ∧
    (∀ (g yhat : finiteAdelicGL2Subgroup ℚ) (i : Fin m),
      (∀ p : ↥SQ, ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range,
        ∃ u ∈ U p, n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (yhat : AdelicGL2 (𝓞 ℚ) ℚ) = yy i p) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v (yhat : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      Wfd (g * yhat * hμf) *
          (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
            (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * yhat : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
              ((transposeInv3 (iotaGL (yy i p)))⁻¹ * k₀ p))) =
        (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) *
          ∑ β : Fin m, (∏ p : ↥SQ, w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (yy i p))) * R β (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by sorry
