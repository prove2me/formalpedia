-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_flatSection_mul_whittaker_iotaGL_diagUnits2_longWeyl3_of_gauge
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_flatSection_mul_whittaker_iotaGL_diagUnits2_longWeyl3_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/32493e7a-c273-5e32-a692-ec15dd666585
-- title:
--   Convergence of two intermediate GL₃timesGL₂ local integrals
-- statement:
--   Fix a nonzero prime $p$ of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$ and write $F$ for the completion $\mathbb{Q}_p$, $|\cdot|$ for `modulus` (the module of $F$, defined by the distributive Haar character, and equal to the norm by [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm)). Let $\theta$ be an additive character of $F$ and $W:\mathrm{GL}_3(F)\to\mathbb{C}$ satisfy: the Whittaker law $W(n(x,y,z)h)=\theta(x+y)W(h)$ for $n(x,y,z)=\begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$; right invariance under some open subgroup of $\mathrm{GL}_3(F)$; a central character $\omega$, i.e. $W(z\cdot 1\cdot h)=\omega(z)W(h)$; and a two-parameter gauge bound: with $\alpha_1(h)=|\det h|\cdot L(h)/M(h)^2$ and $\alpha_2(h)=M(h)/L(h)^2$, where $L(h)$ is the maximum of the norms of the three entries of the last row of $h$ and $M(h)$ the maximum of the norms of the three $2\times2$ minors of its last two rows, there are $B$, $t\in\mathbb{N}$, $C$ with $W(h)=0$ unless $\alpha_1(h)\le B$ and $\alpha_2(h)\le B$, and $\|W(h)\|\le C/(\alpha_1(h)\alpha_2(h))^t$ on that region. Let $\chi_0,\chi_1$ be quasi-characters of $F^\times$, each trivial on the set of units $u$ with $|u|=1$ and (for a given level $c_i$, unless $c_i=0$) $|u-1|\le q^{-c_i}$ in the sense of `higherUnitsAt`. Let $\chi_{u,0}=\chi_0|\cdot|^{u}$, $\chi_{u,1}=\chi_1|\cdot|^{-u}$ and let $f_u$ lie, for every $u\in\mathbb{C}$, in the $\mathbb{C}$-submodule `principalSeries2` of locally constant functions on $\mathrm{GL}_2(F)$ that are left invariant under upper unipotents and transform under the diagonal torus by $\chi_{u,\bullet}$ times the half-modulus. Let $w_0\in\mathrm{GL}_2(F)$ be the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then, with the Borel measurable structure on $F$: for every additive Haar measure $\nu$ on $F$ and Haar measure $\tau$ on $F^\times$ there is $u_2\in\mathbb{R}$ such that for every $u$ with $\operatorname{Re}u>u_2$ there are $\sigma_a<\sigma_b$ for which, for all $s$ with $\sigma_a<\operatorname{Re}s<\sigma_b$, both of the following functions of $(y,(a,t))\in F\times(F^\times\times F^\times)$ are integrable against $\nu\otimes\tau\otimes\tau$: the product of $f_u(w_0\,n(y))$, the character factor $\chi_{u,1}(a)^{-1}\omega(a)^{-1}|a|^{s}\cdot\chi_{u,0}(t)|t|^{-s-1}$, and $W\!\left(\iota(\mathrm{diag}(ta,a))\,w_3\,n_{13}(y)\,w'\right)$; and the same expression with $f_u(w_0\,n(y))$ replaced by $f_u\big(w_0\,{}^{t}(w_0n(y))^{-1}\big)$ and the $\mathrm{GL}_3$ argument replaced by $\iota(\mathrm{diag}(ta,a))\,w_3\,n_{13}(-y)\,w_3\,w'$. Here $\iota$ is the block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$, $n_{13}(c)=1+c\,e_{13}$, $w_3$ the antidiagonal long Weyl element and $w'$ the transposition of the last two coordinates. Only integrability is asserted, not any equality of the two integrals.
--
--   These are the absolute convergence statements for the two intermediate integrals that occur, after the $\mathrm{GL}_3\times\mathrm{GL}_1$ functional equations have been applied inside the unfolded local $\mathrm{GL}_3\times\mathrm{GL}_2$ integral, in the proof of multiplicativity of the local gamma factor in the $\mathrm{GL}_2$ variable for a principal-series partner; the convergence holds on a common non-empty vertical strip in $s$ once $\operatorname{Re}u$ is large, in the deformed range of Jacquet–Piatetski-Shapiro–Shalika. The result is used by [`LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2`](thm.html#LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2), where it turns a measure-preserving change of variables into an identity of absolutely convergent integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_flatSection_mul_whittaker_iotaGL_diagUnits2_longWeyl3_of_gauge.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_flatSection_mul_whittaker_iotaGL_diagUnits2_longWeyl3_of_gauge
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ : AddChar (p.adicCompletion ℚ) ℂ) (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn θ W)
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : LocalGL3 p),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (fu : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (χu : ℂ → Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχu0 : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((χu u 0 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ u))
    (hχu1 : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((χu u 1 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-u)))
    (hfu : ∀ u : ℂ, fu u ∈ principalSeries2 p (χu u))
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
      (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure],
      ∃ u₂ : ℝ, ∀ u : ℂ, u₂ < u.re →
        ∃ σa σb : ℝ, σa < σb ∧ ∀ s : ℂ, σa < s.re → s.re < σb →
          Integrable (fun yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
            fu u (w₀p * upperUnipotent2 p yat.1) *
              (((((χu u 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                  ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χu u 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
                (longWeyl3 * upperUnipotent3 0 0 yat.1 * weylPrime3))))
            (ν.prod (τ.prod τ)) ∧
          Integrable (fun yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
            fu u (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p yat.1)) *
              (((((χu u 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                  ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χu u 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
                (longWeyl3 * upperUnipotent3 0 0 (-yat.1) * longWeyl3 * weylPrime3))))
            (ν.prod (τ.prod τ)) := by sorry
