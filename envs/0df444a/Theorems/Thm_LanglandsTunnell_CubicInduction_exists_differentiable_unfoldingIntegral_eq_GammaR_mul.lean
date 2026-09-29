-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul
-- name    : LanglandsTunnell.CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/ac8b06bd-4ac7-5069-9cdb-eda1d666b543
-- title:
--   Archimedean unfolding integral equals Γ_ℝ times an entire function
-- statement:
--   Fix $u_3\in\mathbb C$, a parity $a_3\in\mathbb Z/2$, a real archimedean parameter $P_2$ (either a principal parameter $(u_1,a_1,u_2,a_2)$ or a discrete one $(u,k)$), and a datum $D$ of type `ArchDatumR P₂`, which packages a Whittaker-type function $W$ on real $2\times2$ matrices with its unipotent and central transformation laws, smoothness and decay properties, together with an entire function `D.zetaEntire` of $(g,u,a,s)$ and an abscissa `D.zeta_abscissa` beyond which the zeta integrals of $W$ converge and equal the archimedean factor of the twist of $P_2$ times `D.zetaEntire`. Let $S$ be a polynomial-times-Gaussian function on real $2\times3$ matrices, that is $S(M)=p\bigl((M_{ib})\bigr)\exp\bigl(-\pi\sum_{i,b}M_{ib}^2\bigr)$ for some complex polynomial $p$ in the six entries. Let $a\in\mathbb Q$ be non-zero and let $\psi_\infty$ be the additive character $x\mapsto\psi_{\mathrm{arch}}(ax)$ of the infinite adele ring of $\mathbb Q$, where $\psi_{\mathrm{arch}}$ is the standard archimedean character. Let $c_0\in\mathbb R$ satisfy $-\operatorname{Re}\mu<c_0$ and $-\operatorname{Re}\nu<c_0$ for all $\mu$ in the real gamma multiset and all $\nu$ in the complex gamma multiset of every twist $P_2\otimes(0,a)$, $a\in\mathbb Z/2$. Finally let $\kappa\in\mathbb R$, let $g_\infty\in\mathrm{GL}_3$ of the infinite adele ring of $\mathbb Q$ with real matrix $m=$ `realMat` $g_\infty$, and let $t\in\mathbb C$, $e\in\mathbb Z$. Then there is an entire function $P:\mathbb C\to\mathbb C$ which on each vertical strip $\sigma_1\le\operatorname{Re}s\le\sigma_2$ satisfies a bound $\|P(s)\|\le C\exp(A|\operatorname{Im}s|)$ for suitable $C,A$, and such that for every $s$ with $\max(c_0,-\operatorname{Re}u_3)-\operatorname{Re}t<\operatorname{Re}s$ and `D.zeta_abscissa` $<\operatorname{Re}s+\operatorname{Re}t$ one has
--   $$\kappa\,\chi_{u_3+1,a_3}(\det m)\int_{x}\; I_{\psi_\infty,S}(x,m)\,\chi_{u_3+2,a_3}(\det x)\,|\det x|^{-2}\,\mathrm{Z}_D\bigl(\mathrm{diag}(a,1)\,x^{-1},t,e\bmod 2,s\bigr)\,dx=\Gamma_{\mathbb R}\bigl(s+u_3+t+\delta(a_3+e)\bigr)P(s),$$
--   where the integral is over all $2\times2$ real matrices $x$ for the standard measure, $\chi_{u,a}(y)=|y|^u$ times $\mathrm{sign}(y)$ if $a\neq0$ and $1$ if $a=0$, $\mathrm{Z}_D=$ `D.zetaEntire`, $\delta(b)=0$ for $b=0$ and $1$ otherwise, and $I_{\psi_\infty,S}(x,m)=\int_{v\in\mathbb R^2}S\bigl(x\cdot(m_{0b}+v_0m_{2b},\,m_{1b}+v_1m_{2b})_b\bigr)\psi_\infty(-v_1)\,dv$ is the Godement inner integral, the real number $-v_1$ being embedded diagonally in the infinite adele ring.
--
--   This is the archimedean local computation in the unfolding of a Godement-type section against the Whittaker datum for the cubic induction used in the Langlands–Tunnell step: it exhibits the archimedean factor of the triple integral as the expected real gamma factor $\Gamma_{\mathbb R}(s+u_3+t+\delta)$ times a function entire and of finite exponential order on vertical strips, as required by the hypotheses of the converse theorem. It is used by [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul
    (u₃ : ℂ) (a₃ : ZMod 2)
    (P₂ : RealArchParam)
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (κ : ℝ)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℂ) (e : ℤ) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
      ∀ s : ℂ, max c₀ (-(u₃).re) - t.re < s.re → D.zeta_abscissa < s.re + t.re →
        (κ : ℂ) *
          (ArchR.quasiChar (u₃ + 1) a₃ (StandardKernel.realMat gInf).det *
            ∫ x : Fin 2 → Fin 2 → ℝ,
              godementInner3 psiInf S (Matrix.of x) (StandardKernel.realMat gInf) *
                ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of x).det *
                  (((|(Matrix.of x).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                D.zetaEntire (ArchR.diagOne (a : ℝ) * (Matrix.of x)⁻¹) t (e : ZMod 2) s) =
          Complex.Gammaℝ (s + (u₃ + t + LanglandsTunnell.signShift (a₃ + (e : ZMod 2)))) * P s := by sorry
