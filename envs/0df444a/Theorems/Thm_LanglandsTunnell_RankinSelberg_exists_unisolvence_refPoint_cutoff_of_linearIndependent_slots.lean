-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots
-- name    : LanglandsTunnell.RankinSelberg.exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/71edd861-6979-5409-b42e-0383d3f9a4b7
-- title:
--   Unisolvence points, reference points and cut-off subgroups at S_Q
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, let `pins` be a carrier-pin package for $\mathbb Q$ (measure, fundamental domain, central subgroup, level subgroups, local generators and an additive measure on the adeles), let $\psi$ be an additive character of the adeles of $\mathbb Q$, let $\mu$ be a character of the idele units of $K$, and let $F$ be a cubic induction form for $(K,\mathrm{pins},\psi,\mu)$, so in particular it carries local Whittaker functions $F.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3(\mathbb Q_v)$. Assume `hBad`: for every finite set $T$ of finite places, at each $v\in T$ that is bad for $(K,\mu)$ (ramified in $K$, or twist-ramified above) the function $F.\mathrm{whittakerLoc}\,v$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb Q_v)$, and every nonzero $W$ in the span of the right translates of $F.\mathrm{whittakerLoc}\,v$ has $F.\mathrm{whittakerLoc}\,v$ in the span of its own right translates. Let $S_Q$ be a finite set of finite places, $m\in\mathbb N$, and for each $p\in S_Q$ and $\alpha<m$ let $w_{p,\alpha}:\mathrm{GL}_2(\mathbb Q_p)\to\mathbb C$ be a function admitting an open right stabiliser, the $m$ products $y\mapsto\prod_{p\in S_Q}w_{p,\alpha}(y_p)$ on $\prod_{p\in S_Q}\mathrm{GL}_2(\mathbb Q_p)$ being linearly independent over $\mathbb C$. Let $w_0\in\mathrm{GL}_2(\mathbb Q)$, and for each $p\in S_Q$ let $W^b_p$ lie in the span of the right translates of $F.\mathrm{whittakerLoc}\,p$ with $W^b_p(\iota(1))=1$, where $\iota$ is the block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$. Then there exist points $y^{(i)}\in\prod_{p\in S_Q}\mathrm{GL}_2(\mathbb Q_p)$ for $i<m$, elements $k_{0,p}\in\mathrm{GL}_3(\mathbb Q_p)$, and subgroups $U_p\le\mathrm{GL}_2(\mathbb Q_p)$ such that: each $U_p$ is open; $F.\mathrm{whittakerLoc}\,p\,(w_3k_{0,p})\neq0$ for the long Weyl element $w_3=$ `longWeyl3`; the $m\times m$ matrix with entries $\prod_{p\in S_Q}w_{p,j}\bigl(w_{0,p}\cdot{}^{t}(y^{(i)}_p)^{-1}\bigr)$, where $w_{0,p}$ is the image of $w_0$ in $\mathrm{GL}_2(\mathbb Q_p)$, has nonzero determinant; for all $u\in U_p$, all $\beta,i<m$, $w_{p,\beta}\bigl(w_{0,p}\cdot{}^{t}(u\,y^{(i)}_p)^{-1}\bigr)=w_{p,\beta}\bigl(w_{0,p}\cdot{}^{t}(y^{(i)}_p)^{-1}\bigr)$; and for all $u\in U_p$, $F.\mathrm{whittakerLoc}\,p\,\bigl(w_3\cdot{}^{t}\iota(u)^{-1}\cdot k_{0,p}\bigr)=F.\mathrm{whittakerLoc}\,p\,(w_3k_{0,p})$.
--
--   This is the unisolvence step in the analysis of global Rankin–Selberg integrals for the cubic induction form: finitely many linearly independent products of local slot functions are evaluated at finitely many points with invertible evaluation matrix, simultaneously with a choice of reference points $k_{0,p}$ at which the local $\mathrm{GL}_3$ Whittaker functions are nonvanishing and of open cut-off subgroups under which all of this data is right invariant. It is obtained from the general non-vanishing determinant statement [`exists_det_of_apply_ne_zero_of_linearIndependent`](thm.html#exists_det_of_apply_ne_zero_of_linearIndependent) for linearly independent families, and serves the isolation of remainder terms in [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_cutoff_remainder_mul_finprod_away`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_cutoff_remainder_mul_finprod_away).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ μ)
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (_hwsm : ∀ (p : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g)
    (w₀ : GL (Fin 2) ℚ)
    (_hind : LinearIndependent ℂ (fun α : Fin m => fun y : (∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) => ∏ p : ↥SQ, w p α (y p)))
    (Wb : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ)
    (_hWbmem : ∀ p : ↥SQ, Wb p ∈ gl3CyclicSubspace (F.whittakerLoc p.1))
    (_hWbone : ∀ p : ↥SQ, Wb p (iotaGL 1) = 1) :
    ∃ (yy : Fin m → ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
      (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
      (∀ p : ↥SQ, IsOpen (U p : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))) ∧
      (∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0) ∧
      ((Matrix.of fun i j : Fin m => ∏ p : ↥SQ,
        w p j (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))).det ≠ 0) ∧
      (∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
        w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (u * yy i p)) =
          w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))) ∧
      (∀ (p : ↥SQ), ∀ u ∈ U p,
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
          F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)) := by sorry
