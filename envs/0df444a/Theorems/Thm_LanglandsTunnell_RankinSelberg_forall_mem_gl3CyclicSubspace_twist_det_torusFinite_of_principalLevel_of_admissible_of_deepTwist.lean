-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist
-- name    : LanglandsTunnell.RankinSelberg.forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a60a413e-dc4c-56f1-a425-64230eee3ba8
-- title:
--   Torus finiteness for the cyclic space of a deep twist
-- statement:
--   Let $p$ be a prime of $\mathbb{Z}=\mathcal O_{\mathbb Q}$, let $W_0:\mathrm{GL}_3(\mathbb Q_p)\to\mathbb C$ satisfy the Whittaker law $W_0(u(x,y,z)g)=\psi_p^{-1}(x+y)W_0(g)$ for the inverse of the standard local additive character, let $d\in\mathbb N$ and assume $W_0(gk)=W_0(g)$ for all $g$ and all $k$ in the maximal compact subgroup of $\mathrm{GL}_3(\mathbb Q_p)$ (entries of $k$ and of $k^{-1}$ of valuation $\le 1$) with $v(k_{ij}-\delta_{ij})\le q^{-d}$, and that $W_0(\mathrm{diag}(t,t,t)h)=\omega_0(t)W_0(h)$ for a character $\omega_0$ of $\mathbb Q_p^\times$. Let $\chi$ be a unitary character of $\mathbb Q_p^\times$ with conductor exponent $k_p$ (trivial on the $k_p$-th higher units, non-trivial on the $m$-th for every $m<k_p$), and put $W_3=(\chi\circ\det)\cdot W_0$. Assume the admissibility hypothesis: for every open subgroup $U_v\le\mathrm{GL}_3(\mathbb Q_p)$ there is a finite set $B$ of functions such that every member of the cyclic subspace spanned by the right translates of $W_3$ which is right $U_v$-invariant lies in the $\mathbb C$-span of $B$. Let $b\in\mathbb N$, let $\varpi$ be a uniformiser (nonzero image, valuation $q^{-1}$), and assume $6(b+3d+3)+7\le k_p$. Then for every $W$ in that cyclic subspace, every $g_3\in\mathrm{GL}_3(\mathbb Q_p)$, $k_0\in\mathrm{GL}_2(\mathbb Q_p)$, every character $\eta$ of $\mathbb Q_p^\times$ of conductor exponent $c\le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$ (Borel structure from the valuation topology), there is a single finite set $T\subseteq\mathbb Z\times\mathbb Z$ such that for all $n=(n_1,n_2)\notin T$ both of the following vanish: the integral over the units $u$ with $v(u)=1$, against the multiplicative Haar measure obtained from the self-dual additive measure at $p$, of $\eta(u)$ times $\int_{K} W\big(\iota(\mathrm{diag}(\varpi,\varpi)^{n_2}\,\mathrm{diag}(\varpi^{n_1}u,1)\,(k_0k)\big)\,g_3\big)\,d\mu_2(k)$, where $\iota$ is the block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ and $K$ is the local level-one subgroup at $p$ of level $p^b$; and the same expression with $W(\,\cdot\,)$ replaced by the dual Whittaker function $g\mapsto W(w_3\,{}^t g^{-1} g_3)$ of $x\mapsto W(xg_3)$ and with $k$ replaced by ${}^tk^{-1}$ in the argument.
--
--   This is the torus-finiteness clause for the two-variable $\eta$-twisted, level-$p^b$-averaged torus integrals attached to a deeply twisted $\mathrm{GL}_3$ Whittaker function: outside a finite set of shell parameters all such integrals vanish, because the exponents of the twisted space on the units have exact conductor exponent larger than that of $\eta$. It feeds the cubic-induction step [`LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_torusFinite_of_cubicInductionForm_twisted_noFE32_level`](thm.html#LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_torusFinite_of_cubicInductionForm_twisted_noFE32_level) in the Rankin–Selberg/converse-theorem part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₀ : LocalGL3 p → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀)
    (d : ℕ)
    (hW₀lev : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (ω₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₀ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₀ t : ℂˣ) : ℂ) * W₀ h)

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace
        (fun g : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g),
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hkβ : 6 * (b + 3 * d + 3) + 7 ≤ kp) :
    ∀ W ∈ gl3CyclicSubspace (fun g : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g),
    ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : ℕ),
    LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 := by sorry
