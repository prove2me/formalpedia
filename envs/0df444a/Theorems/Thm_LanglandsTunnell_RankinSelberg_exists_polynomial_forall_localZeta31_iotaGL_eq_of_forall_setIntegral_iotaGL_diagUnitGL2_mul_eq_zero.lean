-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
-- name    : LanglandsTunnell.RankinSelberg.exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ac654034-7f04-595d-aa6d-3e5d1529c09a
-- title:
--   Laurent-polynomial form of the local (3,1) zeta integral at ι(h)
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and write $F$ for the completion $\mathbb{Q}_p$ at $p$, with valuation ring $\mathcal{O}_F$. Let $\varpi \in \mathcal{O}_F$ have nonzero image in $F$ and valuation $\exp(-1)$, let $\theta$ be an additive character of $F$ with values in $\mathbb{C}$ that is nontrivial (some $x$ has $\theta(x)\neq 1$), and let $W : \mathrm{GL}_3(F) \to \mathbb{C}$ satisfy the Whittaker law $W(n(x,y,z)g) = \theta(x+y)\,W(g)$ for all $x,y,z \in F$ and $g$, where $n(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y,z$, and be right invariant under some open subgroup $U_v \le \mathrm{GL}_3(F)$. Let $\chi : F^\times \to \mathbb{C}^\times$ be a homomorphism and $h \in \mathrm{GL}_2(F)$; write $\iota$ for the embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$, $g \mapsto \mathrm{diag}(g,1)$, $a \mapsto \mathrm{diag}(a,1)$ for the torus element of $\mathrm{GL}_2$, $u(x) = 1 + x e_{21} \in \mathrm{GL}_3(F)$, and $|\cdot|$ for the module of $F$ (the distributive Haar character, extended by $0$). Equip $F$ with its Borel $\sigma$-algebra. Then for every Haar measure $\tau$ on $F^\times$ and every additive Haar measure $\nu$ on $F$, assume: (i) for every $h' \in \mathrm{GL}_2(F)$ there is a finite set $T \subset \mathbb{Z}$ such that $\int_{|u| = 1} W\bigl(\iota(\mathrm{diag}(\varpi^n u,1)\,h')\bigr)\chi(u)\,d\tau(u) = 0$ for all $n \notin T$ (the unit set being $\{u : \mathrm{v}(u) = 1\}$); and (ii) for every $W'$ in the $\mathbb{C}$-span of the right translates $g \mapsto W(gh')$ of $W$ there is $\sigma_0$ with $a \mapsto W'(\iota(\mathrm{diag}(a,1))\,\iota(h))\,\chi(a)\,|a|^{s-1}$ $\tau$-integrable whenever $\operatorname{Re} s > \sigma_0$. The conclusion is that there are a polynomial $P \in \mathbb{C}[X]$, an integer $m$ and a real $\sigma_1$ such that for $\operatorname{Re} s > \sigma_1$ the function $(a,x) \mapsto W(\iota(\mathrm{diag}(a,1))\,u(x)\,\iota(h))\,\chi(a)\,|a|^{s-1}$ is $\tau \otimes \nu$-integrable and the iterated integral $\int_{F^\times}\bigl(\int_F W(\iota(\mathrm{diag}(a,1))u(x)\iota(h))\,d\nu(x)\bigr)\chi(a)|a|^{s-1}\,d\tau(a)$ equals $N(p)^{ms}\,P\bigl(N(p)^{-s}\bigr)$, where $N(p)$ is the absolute norm of $p$.
--
--   This is the local rationality statement for the $(3,1)$ Rankin–Selberg zeta integral with unipotent integration, in the form of Jacquet–Piatetski-Shapiro–Shalika: torus finiteness of $W \circ \iota$ along all of $\mathrm{GL}_2(F)$, together with convergence of the $(3,0)$ integrals of the cyclic space of $W$, forces the $(3,1)$ integral at $\iota(h)$ to be a Laurent polynomial in $N(p)^{-s}$ on a right half-plane. It is used, for $W$ and for its dual, in the two results that transport a pointwise rational functional equation through the outer integrations of an unfolded $\mathrm{GL}_3 \times \mathrm{GL}_2$ integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (θ : AddChar (p.adicCompletion ℚ) ℂ) (hθ : ∃ x : p.adicCompletion ℚ, θ x ≠ 1)
    (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn θ W)
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (h : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],

      (∀ h' : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          W (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
            ^ n * u) * h')) * ((χ u : ℂˣ) : ℂ) ∂τ = 0) →

      (∀ W' ∈ gl3CyclicSubspace W, ∃ σ₀ : ℝ, IsLocalZeta30ConvergentAbove p τ W' χ (iotaGL h) σ₀) →
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₁ : ℝ),
        IsLocalZeta31ConvergentAbove p τ ν W χ (iotaGL h) σ₁ ∧
        ∀ s : ℂ, σ₁ < s.re →
          localZeta31 p τ ν W χ s (iotaGL h) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
