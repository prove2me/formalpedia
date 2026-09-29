-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
-- name    : LanglandsTunnell.CubicInduction.exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/6a6c452c-1446-5b74-9de0-7611153b2072
-- title:
--   Integrable majorant and measurability for the GL₃ Jacquet integrand
-- statement:
--   Fix an archimedean parameter $P$ (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$), a complex $u_3$, a sign $a_3\in\mathbb{Z}/2$, a rational $a\neq 0$, and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ which is the standard archimedean character $x\mapsto \mathrm{psiArch}(x)$ (the finite product over infinite places of the local characters) precomposed with multiplication by the image of $a$. Let $D$ be an `ArchDatumR P`, that is a function $W$ on real $2\times 2$ matrices, smooth on the invertible locus, transforming by $\psi$ under left unipotent translation and by the central character of $P$ times $|z|$ under scaling, with entire zeta integrals satisfying the functional equation for $P$, of finite order in vertical strips, and with the prescribed decay near infinity and near zero. Let $S$ lie in `polyGauss3`, i.e. $S(M)=\mathrm{eval}(M)(p)\cdot \mathrm{gaussian3}(M)$ for some complex polynomial $p$ in the six entries of $M\in \mathbb{R}^{2\times 3}$. Let $c_0\in\mathbb{R}$ satisfy, for both signs $a\in\mathbb{Z}/2$, that $-\mathrm{Re}\,\mu<c_0$ for all $\mu$ in the real gamma-shift multiset of $P$ twisted by $(0,a)$ and $-\mathrm{Re}\,\nu<c_0$ for all $\nu$ in its complex gamma-shift multiset. Write $I(A,e)$ for `jacquetIntegrand3 D u₃ a₃ A psiInf S g e`, the product of the Godement pairing $\mathrm{godementInner3}(\psi_\infty,S)$ of the $2\times 2$ array $e$ against the real $3\times 3$ matrix attached to $g$, the quasi-character with parameter $u_3+2$ and sign $a_3$ evaluated at $\det e$, the factor $(|\det e|^{2})^{-1}$, and $W(\mathrm{diagOne}(A)\cdot e^{-1})$. The assertion is a conjunction of four statements. First, for every $g_0\in \mathrm{GL}_3$ of the infinite adele ring of $\mathbb{Q}$ and every real $q>\max(c_0,-\mathrm{Re}\,u_3)$ there are a neighbourhood $U$ of $g_0$ and a Lebesgue-integrable $F:(\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{R})\to\mathbb{R}$ with $\|I(A,e)\|\le |A|^{1-q}F(e)$ for all $g\in U$, all real $A\neq 0$ and all $e$. Second, for every $g$ the map $(A,e)\mapsto I(A,e)$ is almost everywhere strongly measurable for the product of Lebesgue measures. Third, for every real $p>-2$ the function $e\mapsto \sqrt{e_{00}^2+e_{10}^2}^{\,p}\,(1+\|e\|)^{-(4\max(p,0)+8)}$ is Lebesgue-integrable. Fourth, for every $g$ the function $e\mapsto I(a,e)$, at the real number $a$, is almost everywhere strongly measurable.
--
--   This collects the analytic input — a locally uniform integrable majorant in the dilation variable, joint measurability, and integrability of the auxiliary weight on $2\times2$ arrays — needed to apply dominated convergence and Fubini to the integral defining the explicit archimedean Whittaker (Jacquet) vector for $\mathrm{GL}_3$ built from a polynomial-times-Gaussian section. It is used by the family of identities expressing that vector, for the various harmonic and determinant-twisted sections, as an explicit constant times a real gamma factor times a Mellin transform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
    {P : RealArchParam} (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (D : ArchDatumR P)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀)) :
    (∀ (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)) (q : ℝ), max c₀ (-u₃.re) < q →
      ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
        ∀ g ∈ U, ∀ A : ℝ, A ≠ 0 → ∀ e : Fin 2 → Fin 2 → ℝ,
          ‖jacquetIntegrand3 D u₃ a₃ A psiInf S g e‖ ≤ |A| ^ (1 - q) * F e) ∧
    (∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      AEStronglyMeasurable
        (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) => jacquetIntegrand3 D u₃ a₃ p.1 psiInf S g p.2) (volume.prod volume)) ∧
    (∀ p : ℝ, -2 < p →
      Integrable
        (fun e : Fin 2 → Fin 2 → ℝ =>
          Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8)))
        volume) ∧
    (∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g) volume) := by sorry
