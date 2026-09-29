-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_primalMiddleDatum_rsLocalIntegral_mul_eq_of_iotaGL_invariant_of_dominant
-- name    : LanglandsTunnell.CubicInduction.exists_primalMiddleDatum_rsLocalIntegral_mul_eq_of_iotaGL_invariant_of_dominant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/6b5d2575-3ebe-547f-a4a4-62cf872e557a
-- title:
--   Primal middle datum for the local GL₃timesGL₂ integral
-- statement:
--   Throughout, $v$ is a nonzero prime of $\mathcal O_{\mathbb Q}$, $\mathbb Q_v$ its completion, $q=\mathrm{absNorm}(v)$ the absolute norm of the corresponding ideal, $\nu=$ `selfDualHaarAt ℚ v` the self-dual additive Haar measure on $\mathbb Q_v$ (the Haar measure giving the integers mass $1$, scaled by $q^{-n/2}$ where $n$ is the level `addCharLevel` of the standard character), and $\mu_v^{\times}=$ `Measure.comap Units.val (mulMeasure ν)` the induced multiplicative measure on $\mathbb Q_v^{\times}$. Write $\iota=$ `iotaGL` for the embedding $h\mapsto\begin{pmatrix}h&0\\0&1\end{pmatrix}$ of $\mathrm{GL}_2$ into $\mathrm{GL}_3$, $u_3(x,y,z)$ for the upper unipotent matrix with entries $x,y,z$ above the diagonal, $n_{21}(x)=$ `lowerUnipotent21 x`, $w_3=$ `longWeyl3` (the antidiagonal permutation matrix) and $w'=$ `weylPrime3` (the transposition of the last two coordinates), $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $\mathrm{diag}$ for the obvious diagonal elements, $|a|=$ `modulus a` (the module of $a$, $0$ for $a=0$), and ${}^{t}g^{-1}=$ `transposeInv3 g`. For $W$ on $\mathrm{GL}_3(\mathbb Q_v)$, `gl3CyclicSubspace W` is the $\mathbb C$-span of the right translates $h\mapsto W(\cdot\,h)$, `dualWhittakerFn3 W` is $g\mapsto W(w_3\,{}^{t}g^{-1})$, and the zeta integrals are
--   $$Z_{3,0}(W,\chi,s,g)=\int_{\mathbb Q_v^\times}W(\iota(\mathrm{diag}(a,1))g)\chi(a)|a|^{s-1}\,d\mu^\times,\qquad Z_{3,1}(W,\chi,s,g)=\int_{\mathbb Q_v^\times}\Big(\int_{\mathbb Q_v}W(\iota(\mathrm{diag}(a,1))n_{21}(x)g)\,d\nu\Big)\chi(a)|a|^{s-1}\,d\mu^\times,$$
--   with `localZetaDual31` $(W,\chi,s,g)=Z_{3,1}(\mathrm{dualWhittakerFn3}\,W,\chi^{-1},s,w'\,{}^{t}g^{-1})$, and the predicates `IsLocalZeta30ConvergentAbove`, `IsLocalZeta31ConvergentAbove` asserting integrability of the respective integrands (on $\mathbb Q_v^\times$, resp. on $\mathbb Q_v^\times\times\mathbb Q_v$) for all $s$ with $\mathrm{Re}\,s$ above the given abscissa.
--
--   The data of the theorem are: an additive character $\psi_v$ of $\mathbb Q_v$ with $\psi_v=(\mathrm{psiLocal}\,\mathbb Q\,v)^{-1}$ (`hψinv`), the inverse of the standard local character; a function $W:\mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ subject to: `hW`, $W(u_3(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z,g$; `hW1`, $W(1)=1$; `hmult`, the space of $\psi_v$-Whittaker functionals on the cyclic representation `gl3CyclicRep W` has $\mathbb C$-rank at most one; `hirr`, every nonzero $F\in$ `gl3CyclicSubspace W` satisfies $W\in$ `gl3CyclicSubspace F`; `hsm`, there is an open subgroup $U_v\le\mathrm{GL}_3(\mathbb Q_v)$ with $W(gk)=W(g)$ for $k\in U_v$; `hadm`, for every open subgroup $U_v$ there is a finite set $B$ of functions such that every $U_v$-right-invariant member of `gl3CyclicSubspace W` lies in the span of $B$; and the gauge bound `hWgauge`: there are $B\in\mathbb R$, $t\in\mathbb N$, $C\in\mathbb R$ such that, setting $X(h)=\mathrm{detSize}(h)\cdot\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $Y(h)=\mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ (with $\mathrm{detSize}(h)=\|\det h\|$, $\mathrm{lastRowSup}$ the maximum of the norms of the last-row entries, $\mathrm{minorSup}$ the maximum of the norms of the three $2\times2$ minors `bottomMinor` formed from the last two rows), one has $W(h)=0$ whenever not both $X(h)\le B$ and $Y(h)\le B$, and $\|W(h)\|\le C/(X(h)Y(h))^{t}$ whenever $X(h)\le B$ and $Y(h)\le B$. Further, $\omega_v:\mathbb Q_v^\times\to\mathbb C^\times$ is a character which is unitary (`hωu`) and is the central character of $W$ (`hω`: $W(\mathrm{scalar}(t)h)=\omega_v(t)W(h)$); $\varpi$ is an element of the valuation ring whose image $\pi$ in $\mathbb Q_v$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`), i.e. a uniformiser.
--
--   The local functional-equation data consist of polynomials $E,E_d\in\mathbb C[T]$, a scalar $\varepsilon\in\mathbb C$ and $\ell\in\mathbb N$, subject to `h31`: for every $g\in\mathrm{GL}_3(\mathbb Q_v)$ there are a function $P:\mathbb C\to\mathbb C$ and abscissae $\sigma_0,\sigma_1\in\mathbb R$ such that (i) there are polynomials $Q,R$ with $R\ne0$ and $m\in\mathbb N$ with $P(s)R(q^{-s})=Q(q^{-s})q^{ms}$ for all $s$; (ii) $Z_{3,0}$ for $W$ with the trivial character at $g$ converges above $\sigma_0$ and $Z_{3,0}(W,1,s,g)=E(q^{-s})^{-1}P(s)$ for $\mathrm{Re}\,s>\sigma_0$; (iii) $Z_{3,1}$ for `dualWhittakerFn3 W` with the trivial character at $w'\,{}^{t}g^{-1}$ converges above $\sigma_1$, and for all $s$ with $\mathrm{Re}(1-s)>\sigma_1$, `localZetaDual31`$(W,1,1-s,g)=E_d(q^{-(1-s)})^{-1}\bigl(\varepsilon\,q^{\ell(1/2-s)}P(s)\bigr)$; here and below the measures used are $\mu_v^\times$ on $\mathbb Q_v^\times$ and $\nu$ on $\mathbb Q_v$.
--
--   Finally $V:\mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ lies in `gl3CyclicSubspace W` (`hVmem`) and both $V$ (`hVK`) and `dualWhittakerFn3 V` (`hVdK`) satisfy $F(g\,\iota(k))=F(g)$ for all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $\mathrm{GL}_2(\mathbb Q_v)$ obtained by pulling back along `localEmbed` the finite-adelic subgroup `finiteLevelOne` at the unit ideal (it is compact open, and plays the role of $\mathrm{GL}_2(\mathbb Z_v)$); and $a_1,a_2\in\mathbb C$ satisfy $a_1a_2\ne0$ (`ha`).
--
--   The assertion, with $\mathbb Q_v$ and $\mathrm{GL}_2(\mathbb Q_v)$ carrying their Borel structures, is the following. Let $\mu_2$ be a Haar measure on $\mathrm{GL}_2(\mathbb Q_v)$, $\mu_N$ a Haar measure on the range $N$ of `unipotentGL2Hom` (the group of matrices $u(x)$), and let $c_K$ be a real number with $0<c_K$ (`_hcK`) satisfying the unfolding hypothesis `_hK1`: for every additive character $\theta$ of $\mathbb Q_v$, every $W'$ on $\mathrm{GL}_3(\mathbb Q_v)$ which is a $\theta$-Whittaker function in the above sense and is right-invariant under some open subgroup, every pair $\chi=(\chi_0,\chi_1)$ of characters of $\mathbb Q_v^\times$, every $f\in$ `principalSeries2` $v\,\chi$ (locally constant, left invariant under $u(x)$, and transforming under $\mathrm{diag}(a_0,a_1)$ by $\chi_0(a_0)\chi_1(a_1)\sqrt{\|a_0\|/\|a_1\|}$), every $w_0$ whose matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and every $s\in\mathbb C$: if $g\mapsto W'(\iota g)f(w_0g)|\det g|^{s-1/2}$ is $\mu_2$-integrable, then $g\mapsto W'(\iota g)\bigl(\int f(w_0u(y)g)\theta(y)\,d\nu(y)\bigr)|\det g|^{s-1/2}$ is integrable for $\mu_2$ with density [`HaarQuotient.density`](def/HaarQuotient.html#L25) $N\,\mu_N$, and
--   $$\mathrm{rsLocalIntegral}\,\mu_2,N,\mu_N,\ \delta(g)=|\det g|,\ s,\ \bigl(g\mapsto W'(\iota g)\bigr),\ \bigl(g\mapsto\textstyle\int f(w_0u(y)g)\theta(y)d\nu\bigr)$$
--   equals $c_K\int_{\mathbb Q_v}f(w_0u(y))\Bigl(\int_{\mathbb Q_v^{\times}}\chi_0(a)|a|^{s-1}Z_{3,1}\bigl(W',\chi_1,s,\iota(\mathrm{diag}(1,a)u(y))\bigr)d\mu_v^\times(a)\Bigr)d\nu(y)$, where `rsLocalIntegral` $\mu_2,N,\mu_N,\delta,s,W,F=\int(W\cdot F)\delta^{s-1/2}$ against $\mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) $N\,\mu_N$.
--
--   Let further $u\in\mathbb C$ satisfy the dominance condition $\|a_1\|q^{-\mathrm{Re}\,u}<\|a_2\|q^{\mathrm{Re}\,u}$, put $a_1'=a_1q^{-u}$ and $a_2'=a_2q^{u}$, and let $W_2:\mathrm{GL}_2(\mathbb Q_v)\to\mathbb C$ satisfy: `hW₂ψ`, $W_2(u(x)g)=\mathrm{psiLocal}(x)W_2(g)$ for the standard local character; `hW₂K`, $W_2(gk)=W_2(g)$ for $k$ in the local level-one subgroup at the unit ideal; `hW₂1`, $W_2(1)=1$; `hW₂Z`, $W_2(g\cdot\pi I_2)=\frac{a_1'a_2'}{q}W_2(g)$; and `hW₂T`, $W_2(\mathrm{diag}(\pi^{m},1))=\mathrm{torusFactor}(q,\,a_1'+a_2',\,a_1'a_2'/q,\,m)$ for all $m\in\mathbb Z$, where `torusFactor` is $0$ for $m<0$ and otherwise the term $c_m$ of the Hecke recursion $c_0=1$, $c_1=\lambda/N$, $c_{m+2}=(\lambda c_{m+1}-\omega c_m)/N$.
--
--   Then there exist polynomials $m_{1},m_{2}\in\mathbb C[T]$, an integer $k$ and a real $\sigma_P$ with $m_{2}\ne0$ such that both of the following hold. Write $\beta_0=a_1'q^{-1/2}$, $\beta_1=a_2'q^{-1/2}$, $\omega_\varpi=\omega_v(\pi)$ (the value of the central character at the uniformiser viewed as a unit), and
--   $$X_s=\beta_0\,q^{1-s},\qquad Y_s=\beta_1^{-1}\omega_\varpi^{-1}q^{s}.$$
--
--   First conjunct (the primal middle datum property). For all $N_b\in\mathbb Z$, polynomials $D_{b1},D_{b2}\in\mathbb C[T]$, $P_b\in\mathbb C[T_0,T_1]$ and $r_b\in\mathbb R$ such that the coefficients $A(n)=V\bigl(\iota(\pi^{n_2}I_2\cdot\mathrm{diag}(\pi^{n_1},1))\cdot w_3w'\bigr)$, $n\in\mathbb Z^2$, admit the rational presentation expressed by: $D_{b1}(0)\ne0$, $D_{b2}(0)\ne0$, $0<r_b$, $A(n)=0$ whenever $n_1<N_b$ or $n_2<N_b$, and for all $X,Y$ with $\|X\|<r_b$, $\|Y\|<r_b$ the family $\|A(N_b+m_1,N_b+m_2)X^{m_1}Y^{m_2}\|$ ($m\in\mathbb N^2$) is summable and $\bigl(\sum_{m}A(N_b+m_1,N_b+m_2)X^{m_1}Y^{m_2}\bigr)D_{b1}(X)D_{b2}(Y)=P_b(X,Y)$; and for all $N_t,D_{t1},D_{t2},P_t,r_t$ satisfying the same conditions with $A(n)=V\bigl(\iota(\pi^{n_2}I_2\cdot\mathrm{diag}(\pi^{n_1},1))\cdot w'\bigr)$; one has, for every $s\in\mathbb C$,
--   $$m_{1}(q^{-s})\,q^{ks}\,D_{b1}(X_s)D_{b2}(Y_s)\,D_{t1}(X_s)D_{t2}(Y_s)\,q\;=\;m_{2}(q^{-s})\,C(s)\Bigl[X_s^{N_b}Y_s^{N_b}P_b(X_s,Y_s)\,D_{t1}(X_s)D_{t2}(Y_s)\,q\;+\;X_s^{N_t}Y_s^{N_t}P_t(X_s,Y_s)\,D_{b1}(X_s)D_{b2}(Y_s)\Bigr],$$
--   where, with $\nu_0=\nu(\{x:\,v(x)\le1\})$ and $\mu_1=\mu_v^{\times}(\{e:\,v(e)=1\})$ taken as real numbers,
--   $$C(s)=\Bigl(c_K\,\nu_0^{3}\,\mu_1^{2}\bigl(\nu_0\,(1-q^{-1}a_1'(a_2')^{-1})\bigr)^{-1}\Bigr)\varepsilon^{-1}q^{-\ell/2}\bigl(\beta_1q^{-s}\bigr)^{-\ell}E\bigl(a_1'q^{-(s+1/2)}\bigr)E_d\bigl((a_2')^{-1}q^{-(1/2-s)}\bigr).$$
--
--   Second conjunct. For every $s$ with $\sigma_P<\mathrm{Re}\,s$,
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2,N,\mu_N,\ \delta(g)=|\det g|,\ s,\ g\mapsto V(\iota g),\ W_2\bigr)\cdot E\bigl(a_1'q^{-(s+1/2)}\bigr)\cdot E\bigl(a_2'q^{-(s+1/2)}\bigr)\cdot m_{2}(q^{-s})\;=\;m_{1}(q^{-s})\,q^{ks}.$$
--
--   This is the primal half of the common-middle step in the local Rankin–Selberg theory for $\mathrm{GL}_3\times\mathrm{GL}_2$ at a finite place: it produces a single rational datum $(m_1,m_2,k)$ which simultaneously computes the local integral of the $\iota(\mathrm{GL}_2(\mathbb Z_v))$-invariant vector $V$ against the unramified Whittaker function with Satake parameters $(a_1q^{-u},a_2q^{u})$, and satisfies the functional-equation identity relating the two-variable torus series of $V$ along $w_3w'$ and along $w'$. It is used by [`LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge), where the primal and dual halves are matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_primalMiddleDatum_rsLocalIntegral_mul_eq_of_iotaGL_invariant_of_dominant.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.exists_primalMiddleDatum_rsLocalIntegral_mul_eq_of_iotaGL_invariant_of_dominant
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) :
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∀ (cK : ℝ) (_hcK : 0 < cK)
      (_hK1 : ∀ (θ : AddChar (v.adicCompletion ℚ) ℂ)
          (W : LocalGL3 v → ℂ) (_hW : IsGL3PsiWhittakerFn θ W)
          (_hWsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
          (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
          (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (_hf : f ∈ principalSeries2 v χ)
          (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
          (_hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
          (s : ℂ),
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * f (w₀ * g)) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2)) μ₂ →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * (∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v))) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) (fun g => ∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v)) =
            (cK : ℂ) * ∫ y, f (w₀ * unipotentGL2 y) *
              (∫ a, ((χ 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
                localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W (χ 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)),
      ∀ u : ℂ, ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re →
      ∀ (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) / (Ideal.absNorm v.asIdeal : ℂ)) m),
      ∃ (m₁P m₂P : Polynomial ℂ) (kP : ℤ) (σP : ℝ), m₂P ≠ 0 ∧
      (
      ∀ (Nb : ℤ) (Db₁ Db₂ : Polynomial ℂ) (Pb : MvPolynomial (Fin 2) ℂ) (rb : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Db₁.eval 0 ≠ 0 ∧ Db₂.eval 0 ≠ 0 ∧ 0 < rb ∧
          (∀ n : ℤ × ℤ, (n.1 < Nb ∨ n.2 < Nb) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rb → ‖Y‖ < rb →
            Summable (fun m : ℕ × ℕ => ‖A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Db₁.eval X * Db₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pb)
        ) →
      ∀ (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ) (rt : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * weylPrime3)) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Dt₁.eval 0 ≠ 0 ∧ Dt₂.eval 0 ≠ 0 ∧ 0 < rt ∧
          (∀ n : ℤ × ℤ, (n.1 < Nt ∨ n.2 < Nt) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rt → ‖Y‖ < rt →
            Summable (fun m : ℕ × ℕ => ‖A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Dt₁.eval X * Dt₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pt)
        ) →
      ∀ s : ℂ,
        m₁P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s) *
            ((Db₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (Dt₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * ((Ideal.absNorm v.asIdeal : ℂ))) =
          m₂P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹) * ε⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((ℓ : ℂ) / 2)) * ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-(ℓ : ℤ)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) *
            (((((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nb * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nb * MvPolynomial.eval ![((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pb) * (Dt₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * ((Ideal.absNorm v.asIdeal : ℂ)) +
              ((1 : ℂ)) * ((((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nt * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nt * MvPolynomial.eval ![((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pt) * (Db₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)))) ∧
      (∀ s : ℂ, σP < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => V (iotaGL g)) W₂ *
            E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            m₂P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          m₁P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s)) := by sorry
