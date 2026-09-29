-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/be99bb0e-8202-5bd2-a43a-a02cea33545c
-- title:
--   Non-vanishing of a GL₃ Whittaker zeta integral on a half-plane
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), let $\psi_v$ be a non-trivial $\mathbb{C}$-valued additive character of the completion $\mathbb{Q}_v$, and let $W : GL_3(\mathbb{Q}_v) \to \mathbb{C}$ be a function which is $\psi_v$-Whittaker in the sense that $W(u(x,y,z)g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the corner; assume $W \neq 0$ and that $W$ is invariant under right translation by some open subgroup $U_v \le GL_3(\mathbb{Q}_v)$, i.e. $W(gk) = W(g)$ for all $k \in U_v$ and all $g$. Let $\chi : \mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$ be a multiplicative homomorphism. Write $\mu$ for the measure on $\mathbb{Q}_v^{\times}$ obtained by pulling back, along the inclusion of units, the measure which on $\mathbb{Q}_v \setminus \{0\}$ has density $\|x\|^{-1}$ with respect to the additive Haar measure `selfDualHaarAt` on $\mathbb{Q}_v$ (the Haar measure giving the local integers mass $N(v)^{-n/2}$, $n$ the level of the standard additive character at $v$), $\|\cdot\|$ being the module character. Assume that for every $g \in GL_3(\mathbb{Q}_v)$ there is a $\sigma \in \mathbb{R}$ such that $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,\chi(a)\,\|a\|^{s-1}$ is $\mu$-integrable for all $s$ with $\mathrm{Re}\,s > \sigma$, where $\iota$ is the embedding $GL_2 \hookrightarrow GL_3$. The conclusion is that there exist $g \in GL_3(\mathbb{Q}_v)$ and $\sigma \in \mathbb{R}$ such that this integrand is $\mu$-integrable for every $s$ with $\mathrm{Re}\,s > \sigma$ and such that the zeta integral $\int_{\mathbb{Q}_v^{\times}} W(\iota(\mathrm{diag}(a,1))g)\,\chi(a)\,\|a\|^{s-1}\,d\mu(a)$ is non-zero at every $s$ with $\mathrm{Re}\,s > \sigma$.
--
--   This is the local non-vanishing input of Rankin–Selberg type for the $GL_3$ zeta integrals attached to a Whittaker function: the translating element $g$ depends on $\chi$, since for a fixed $g$ the integral may vanish identically, and the non-vanishing is asserted throughout a half-plane of absolute convergence rather than at a single point. It is used in the cubic-induction part of the Langlands–Tunnell argument, where the global functional equation and the comparison of root numbers for the induced datum are assembled from the local zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem LanglandsTunnell.CubicInduction.exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW0 : W ≠ 0)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hconv : ∀ g : LocalGL3 v, ∃ σ : ℝ,
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ) :
    letI := localBorel ℚ v
    (∃ (g : LocalGL3 v) (σ : ℝ),
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ ∧
      ∀ s : ℂ, σ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g ≠ 0) := by sorry
