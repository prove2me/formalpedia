-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe
-- name    : LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b1e4abf8-92f9-5f9f-a981-fd7d3fba7df3
-- title:
--   Local GL₃timesGL₁ functional equation spreads to the cyclic space
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_p$ for the completion of $\mathbb{Q}$ at $p$ and $q=\mathrm{N}p$ for the absolute norm of $p$, and equip $\mathbb{Q}_p$ with the Borel $\sigma$-algebra `localBorel`, the self-dual additive Haar measure `selfDualHaarAt` attached to the standard character, and on $\mathbb{Q}_p^\times$ the measure obtained from $|x|^{-1}\,dx$ by restriction and pullback along $\mathbb{Q}_p^\times\to\mathbb{Q}_p$. Let $W_{3,\mathrm{base}}:\mathrm{GL}_3(\mathbb{Q}_p)\to\mathbb{C}$ be any function, $\eta:\mathbb{Q}_p^\times\to\mathbb{C}^\times$ a homomorphism, $C\in\mathbb{C}$ and $k\in\mathbb{Z}$. Call the package valid for a function $W$ at $g\in\mathrm{GL}_3(\mathbb{Q}_p)$ if there are $Q_1,Q_2\in\mathbb{C}[X]$ with $Q_2\neq 0$, $n\in\mathbb{Z}$ and $\sigma_0,\sigma_1\in\mathbb{R}$ such that: for $\operatorname{Re}s>\sigma_0$ the integrand $a\mapsto W(\iota(\mathrm{diag}(a,1))g)\,\eta(a)\,|a|^{s-1}$ is integrable and $Z_0(s,W,\eta;g)\,Q_2(q^{-s})=Q_1(q^{-s})\,q^{ns}$, where $Z_0$ is `localZeta30`; for $\operatorname{Re}s>\sigma_1$ the function $(a,x)\mapsto \widetilde W(\iota(\mathrm{diag}(a,1))\,u_{21}(x)\,w'\,{}^{t}g^{-1})\,\eta^{-1}(a)\,|a|^{s-1}$ is integrable for the product measure, with $\widetilde W(h)=W(w_3\,{}^{t}h^{-1})$, $w_3$ antidiagonal and $w'$ the transposition of the last two coordinates; and for $\operatorname{Re}(1-s)>\sigma_1$ one has $\widetilde Z(1-s,W,\eta;g)\,Q_2(q^{-s})=Q_1(q^{-s})\,q^{ns}\,\bigl(C\,q^{ks}\bigr)$, where $\widetilde Z$ is `localZetaDual31`. The hypothesis is that the package is valid for $W_{3,\mathrm{base}}$ at every $g$; the conclusion is that it is valid, with the same $C$ and $k$ but with $Q_1,Q_2,n,\sigma_0,\sigma_1$ depending on the data, for every $W_3$ in `gl3CyclicSubspace W₃base`, the $\mathbb{C}$-span of the functions `gl3AmbientRightTranslate h W₃base` for $h\in\mathrm{GL}_3(\mathbb{Q}_p)$, at every $g$.
--
--   This is the linearity step carrying the local $\mathrm{GL}_3\times\mathrm{GL}_1$ functional-equation package of Jacquet, Piatetski-Shapiro and Shalika from a single function, assumed to satisfy it at all of its right translates, to the whole cyclic space that function generates. It is used in the identification of $\mathrm{GL}_3\times\mathrm{GL}_1$ local zeta integrals on that space and in the construction of the primal and dual middle data entering the computation of $\mathrm{GL}_3\times\mathrm{GL}_2$ local Rankin–Selberg integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (C : ℂ) (k : ℤ)
    (h31 : ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base η g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)))) :
    ∀ W₃ ∈ gl3CyclicSubspace W₃base, ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃ η g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃ η s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃ η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s))) := by sorry
