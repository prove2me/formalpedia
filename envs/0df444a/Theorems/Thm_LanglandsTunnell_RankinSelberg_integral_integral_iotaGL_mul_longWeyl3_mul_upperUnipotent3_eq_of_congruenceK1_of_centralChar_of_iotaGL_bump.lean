-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_integral_iotaGL_mul_longWeyl3_mul_upperUnipotent3_eq_of_congruenceK1_of_centralChar_of_iotaGL_bump
-- name    : LanglandsTunnell.RankinSelberg.integral_integral_iotaGL_mul_longWeyl3_mul_upperUnipotent3_eq_of_congruenceK1_of_centralChar_of_iotaGL_bump
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/9a025674-40ec-5892-b802-be3f42ecff1f
-- title:
--   Equal smoothed Whittaker integrals along ι(GL₂)w₃ at level K₁(p^f)
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, let $f$ be a natural number and let $\omega$ be a homomorphism from $(\mathbb Q_p^\times)$ to $\mathbb C^\times$, where $\mathbb Q_p$ denotes the completion `p.adicCompletion ℚ`. Let $W_0, W_0' : GL_3(\mathbb Q_p) \to \mathbb C$ each satisfy: the Whittaker transformation law $W(n(x,y,z)g) = \psi_p^{-1}(x+y)\,W(g)$ for all $x,y,z \in \mathbb Q_p$ and $g$, where $n(x,y,z)$ is the upper unipotent matrix with entries $(1,x,z;0,1,y;0,0,1)$ and $\psi_p$ is the local standard additive character [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65); right invariance $W(gk)=W(g)$ for every $k$ in the set `congruenceK1 (𝓞 ℚ) ℚ p f`, that is, every $k$ with all entries of $k$ and of $k^{-1}$ of valuation $\le 1$ and with $v(k_{20}), v(k_{21}), v(k_{22}-1) \le \exp(-f)$; the central character law $W(\mathrm{scalar}(t)h) = \omega(t)W(h)$ for $t \in \mathbb Q_p^\times$; right invariance $W(\iota(hk)) = W(\iota(h))$ for $k$ in the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback along the local embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of the finite-adelic level-one subgroup for the unit ideal), where $\iota$ is $h \mapsto \mathrm{diag}(h,1)$; the support condition that $W(\iota(h)) \ne 0$ forces $h = \begin{pmatrix}1&x\\0&1\end{pmatrix}k$ for some $x \in \mathbb Q_p$ and some $k$ in that subgroup; and $W(\iota(1)) = 1$. Let $\varphi, \varphi_1 : \mathbb Q_p \to \mathbb C$ be such that $\varphi(u) \ne 0$ and $\varphi_1(y) \ne 0$ imply $y \ne 0$, $v(y^{-1}) \le \exp(-f)$ and $v(y^{-1}u) \le \exp(-f)$. Then, with $\mathbb Q_p$ given its Borel structure `localBorel` and with both integrations taken against the self-dual Haar measure `selfDualHaarAt ℚ p`, for every $g \in GL_2(\mathbb Q_p)$ the iterated Bochner integral $\int\!\int W_0(\iota(g)\,w_3\,n(u,0,y))\,\varphi(u)\varphi_1(y)$ (inner variable $y$, outer variable $u$) equals the same integral with $W_0'$ in place of $W_0$, where $w_3$ is the antidiagonal long Weyl element of $GL_3$.
--
--   This is the local matching step in the Jacquet–Shalika analysis of highly ramified $\varepsilon$-factors: two $\psi_p^{-1}$-Whittaker functions on $GL_3(\mathbb Q_p)$ with the same $K_1(p^f)$-invariance, the same central character and the same restriction along $\iota$ produce the same smoothed integrals over the cell $\iota(GL_2)w_3N$ cut out by the support condition on $\varphi,\varphi_1$. It is used in the construction of test vectors for the local Rankin–Selberg integrals entering the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integral_integral_iotaGL_mul_longWeyl3_mul_upperUnipotent3_eq_of_congruenceK1_of_centralChar_of_iotaGL_bump.lean

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

theorem LanglandsTunnell.RankinSelberg.integral_integral_iotaGL_mul_longWeyl3_mul_upperUnipotent3_eq_of_congruenceK1_of_centralChar_of_iotaGL_bump
    (p : HeightOneSpectrum (𝓞 ℚ)) (f : ℕ)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)

    (W₀ : LocalGL3 p → ℂ)
    (hlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hω : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hbK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbsupp : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k)
    (hb1 : W₀ (iotaGL 1) = 1)

    (W₀' : LocalGL3 p → ℂ)
    (hlaw' : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀')
    (hK1' : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀' (g * k) = W₀' g)
    (hω' : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀' h)
    (hbK' : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      W₀' (iotaGL (h * k)) = W₀' (iotaGL h))
    (hbsupp' : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀' (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k)
    (hb1' : W₀' (iotaGL 1) = 1)

    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hsupp : ∀ u y : p.adicCompletion ℚ, φ u ≠ 0 → φ₁ y ≠ 0 →
      y ≠ 0 ∧ Valued.v y⁻¹ ≤ WithZero.exp (-(f : ℤ)) ∧ Valued.v (y⁻¹ * u) ≤ WithZero.exp (-(f : ℤ))) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      (∫ u, ∫ y, W₀ (iotaGL g * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) =
      (∫ u, ∫ y, W₀' (iotaGL g * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) := by sorry
