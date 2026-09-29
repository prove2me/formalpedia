-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos
-- name    : LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/0ab8bcaa-2b43-5f48-be22-97a77a2ee334
-- title:
--   Level-pᵈ Whittaker vector in a unitary principal series of GL₃
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, with completion $\mathbb Q_p :=$ `p.adicCompletion ℚ`. Let $\lambda_0,\lambda_1,\lambda_2 : \mathbb Q_p^\times \to \mathbb C^\times$ be group homomorphisms, each locally constant and each unitary in the sense that $\|\lambda_i(x)\| = 1$ for all $x$, and let $\chi : \mathbb Q_p^\times \to \mathbb C^\times$ be a further locally constant homomorphism with $\|\chi(x)\| = 1$ for all $x$. Let $d$ be a natural number with $0 < d$, and assume each $\lambda_i \chi^{-1}$ takes the value $1$ on `higherUnitsAt ℚ p d`, the set of units $u$ with $v(u) = 1$ and (since $d \neq 0$) $v(u - 1) \le \exp(-d)$. The conclusion asserts the existence of a $\mathbb C$-linear functional $\Lambda$ on `principalSeries3 p lam` — the space of locally constant $f : GL_3(\mathbb Q_p) \to \mathbb C$ with $f(n(x,y,z)g) = f(g)$ for the upper unipotent matrices $n(x,y,z)$ and $f(\mathrm{diag}(a)g) = \big(\prod_i \lambda_i(a_i)\big)\,(\|a_0\|/\|a_2\|)\,f(g)$ — and of an element $f$ of that space, such that: (i) $\Lambda$ is a Whittaker functional for the inverse of the standard local additive character $\psi_p =$ `psiLocal ℚ p`, i.e. $\Lambda$ applied to the right translate of $F$ by $n(x,y,z)$ equals $\psi_p(x+y)^{-1}\Lambda(F)$ for all $x,y,z$ and all $F$; (ii) the matrix coefficient $W =$ `coefficientFn Λ f`, $W(g) = \Lambda(g \cdot f)$, is not identically zero; and (iii) for every $k$ in `localMaximalCompact3`, i.e. every $k \in GL_3(\mathbb Q_p)$ all of whose entries and all of whose inverse's entries have valuation $\le 1$, satisfying $v(k_{ij} - \delta_{ij}) \le \exp(-d)$ for all $i,j$, and every $g \in GL_3(\mathbb Q_p)$, one has $\chi(\det(gk))^{-1}W(gk) = \chi(\det g)^{-1}W(g)$; that is, the $\chi\circ\det$-untwisting of $W$ is right invariant under the principal congruence subgroup of level $p^d$.
--
--   This is the local existence statement supplying, for a unitary principal series of $GL_3(\mathbb Q_p)$ whose inducing characters agree with $\chi$ up to level $p^d$, a vector with non-vanishing Whittaker coefficient whose $\chi$-untwisting has principal level $d$. It is used by [`LanglandsTunnell.RankinSelberg.exists_principalSeries3_whittaker_deepTwist_centralChar_of_higherUnitsAt_unitary_shallow`](thm.html#LanglandsTunnell.RankinSelberg.exists_principalSeries3_whittaker_deepTwist_centralChar_of_higherUnitsAt_unitary_shallow) in the assembly of local data for the converse-theorem input, and cites the Jacquet-functional construction of Whittaker functionals on `principalSeries3` together with the triviality of $\psi_p$ on the local integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical

theorem LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (d : ℕ) (hd : 0 < d)
    (hlev : ∀ i : Fin 3, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam i * χ⁻¹) u = 1) :
    ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧
      coefficientFn Λ f ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * coefficientFn Λ f (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * coefficientFn Λ f g := by sorry
