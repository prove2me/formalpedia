-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3
-- name    : LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d776c6e8-9a84-56c8-9ae8-269d43b9d11e
-- title:
--   Explicit K₁(p^{3B+Δ})-invariant bump vector for twisted cubic induction
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, equipped with an integral $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$, and let $\nu$ be a character of the ideles of $K$ which is trivial on principal ideles, continuous and unitary. Let $\psi$ be a global additive character of the adeles of $\mathbb{Q}$ (trivial on $\mathbb{Q}$, continuous, non-trivial) whose local component at every finite place has `addCharLevel` $0$, with $\psi^{-1}=$ `psiQ`. Let $F$ be a cubic induction form for $(K,\psi,\nu)$ over the production carrier data attached to the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the levels $\mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators `heckeGen` and the adelic box, with $F.\mathrm{form}\neq 0$ and with $F.\mathrm{whittakerLoc}\,v\,(1)=1$ and induced spherical torus values at every $v$ unramified in $K$ of additive level $0$. Fix a finite place $p$ of $\mathbb{Q}$ and write $W:=F.\mathrm{whittakerLoc}\,p$. Assume: $W$ is right invariant under some open subgroup of $GL_3(\mathbb{Q}_p)$; every non-zero $W'$ in the cyclic span `gl3CyclicSubspace W` has $W$ in its own cyclic span; for each open subgroup $U_v$ the $U_v$-right-invariant vectors of that cyclic span lie in the span of a finite set; $W\neq 0$; $W(\mathrm{scalar}(t)h)=\omega_p(t)W(h)$ for a character $\omega_p$ of $\mathbb{Q}_p^\times$, which is unitary; $W$ is right invariant under the matrices of `localMaximalCompact3` congruent to $1$ entrywise to valuation $\le q^{-d}$; the conductor exponents of the local components of $\nu$ at the primes of $K$ above $p$ are all $\le c_0$; $\xi$ is a unitary character of $\mathbb{Q}_p^\times$ with conductor exponent exactly $B$, where $c_0+6\le B$ and $2d+1\le B$; $F.\mathrm{whittaker}$ is gauge-majorised; and all places outside a finite set $S'$ are not bad for $(K,\nu)$. Fix $\Delta$, polynomials $E=Ed=1$, $\varepsilon\neq 0$ and $1\le \ell\le 3B+\Delta$ such that $\omega_p\xi^3$ is trivial on units $u$ of valuation $1$ with $v(u-1)\le q^{-\ell}$, and assume that at every $g\in GL_3(\mathbb{Q}_p)$ the twisted function $g\mapsto \xi(\det g)W(g)$ satisfies a local $(3,1)$ functional equation with trivial character: there are $P:\mathbb{C}\to\mathbb{C}$, rational in $q^{-s}$ up to a power $q^{ms}$, and abscissae $\sigma_0,\sigma_1$ such that the integrals `localZeta30` and the dual integrals converge in the respective half-planes (for the multiplicative measure attached to the self-dual Haar measure at $p$), with `localZeta30` $=P(s)$ and `localZetaDual31` at $1-s$ equal to $\varepsilon\,q^{\ell(1/2-s)}P(s)$. Then the cyclic span of $g\mapsto \xi(\det g)W(g)$ contains a vector $W_0$ which is right invariant under `congruenceK1` at level $3B+\Delta$ (matrices of `localMaximalCompact3` whose last row is $(0,0,1)$ to valuation $q^{-(3B+\Delta)}$), satisfies $W_0(\iota(hk))=W_0(\iota(h))$ for all $h\in GL_2(\mathbb{Q}_p)$ and all $k$ in the local level-one subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at the unit ideal, vanishes at $\iota(h)$ unless $h=\mathrm{unipotentGL2}(x)\,k$ for some $x\in\mathbb{Q}_p$ and some such $k$, and has $W_0(\iota(1))=1$, where $\iota=$ `iotaGL` is the embedding $h\mapsto \mathrm{diag}(h,1)$.
--
--   This is the local bump-vector construction at a highly ramified twist: from the local Whittaker function of a cubic induction form one extracts, inside its cyclic span, a vector of explicit level $3B+\Delta$ whose restriction along $GL_2\hookrightarrow GL_3$ is supported on $N_2(\mathbb{Q}_p)$ times the local level-one subgroup and normalised at the identity. It supplies the $GL_3$-side hypothesis in the Rankin–Selberg pair-stability argument, and is used in the analytic continuation and factorisation of the $L$-function of the Rankin–Selberg datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)

    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (p : HeightOneSpectrum (𝓞 ℚ))

    (hsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, F.whittakerLoc p (g * k) = F.whittakerLoc p g)
    (hirr : ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc p), W ≠ 0 → F.whittakerLoc p ∈ gl3CyclicSubspace W)
    (hadm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ Bs : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (Bs : Set (LocalGL3 p → ℂ)))
    (hne : F.whittakerLoc p ≠ 0)

    (ωp : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcent : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      F.whittakerLoc p (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωp t : ℂˣ) : ℂ) * F.whittakerLoc p h)
    (d : ℕ)
    (hKd : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 p, F.whittakerLoc p (g * k) = F.whittakerLoc p g)

    (c₀ : ℕ)
    (hν : ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar ν w) c)

    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ξ x : ℂˣ) : ℂ)‖ = 1)
    (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B)
    (hB : c₀ + 6 ≤ B) (hBd : 2 * d + 1 ≤ B)
    (hωu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((ωp z : ℂˣ) : ℂ)‖ = 1)

    (hFg : IsGaugeMajorised3 ℚ F.whittaker)
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hgood : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S' → ¬ IsBadPlace K ν q)

    (Δ : ℕ) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (hE1 : E = 1) (hEd1 : Ed = 1) (hε : ε ≠ 0) (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 3 * B + Δ)
    (hωℓ : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(ℓ : ℤ)) → (ωp * ξ ^ 3) u = 1)
    (h31 : ∀ g : LocalGL3 p,
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ p
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g) 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g) 1 s g =
            (E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)))
          (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) (dualWhittakerFn3 (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g)) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)
              (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g) 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    :
    ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g),
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p (3 * B + Δ), ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
        ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
      W₀ (iotaGL 1) = 1 := by sorry
