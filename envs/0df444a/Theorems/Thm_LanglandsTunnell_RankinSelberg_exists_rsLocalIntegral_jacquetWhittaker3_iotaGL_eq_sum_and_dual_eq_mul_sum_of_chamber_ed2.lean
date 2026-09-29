-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
-- name    : LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/0f9f05c3-27d5-51d8-9cb1-64101f8dc55d
-- title:
--   Unfolded GL₃× GL₂ Rankin–Selberg integrals, primal and dual
-- statement:
--   Throughout, $F$ denotes the completion of $\mathbb Q$ at a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, $\psi$ denotes the local additive character [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) (the component at $p$ of the standard adelic character of $\mathbb Q$), and $\mathrm{mod}(a)$ denotes `modulus a`, the modulus of multiplication by $a$ on $F$ (equal to $0$ at $a=0$). Measurability on $GL_2(F)$ is the Borel structure `localGLBorel ℚ p` and on $F$ the Borel structure `localBorel ℚ p`; `selfDualHaarAt ℚ p` is the additive Haar measure on $F$ self-dual for $\psi$.
--
--   $GL_3$ data: a triple $\lambda=(\lambda_0,\lambda_1,\lambda_2)$ of homomorphisms $F^\times\to\mathbb C^\times$, each locally constant (`hlam`), together with exponents $\sigma:\{0,1,2\}\to\mathbb R$ such that $\|\lambda_i(a)\|=\|a\|^{\sigma_i}$ for all $a\in F^\times$ (`hσ`), lying in the chamber $\sigma_2<\sigma_1<\sigma_0$ (`h12`, `h01`); a function $\Phi$ on $F^3$ that is locally constant with compact support (`hΦ`); an element $T\in GL_3(F)$; and a function $W_3$ on $GL_3(F)$ which, by `hW₃`, is the translate
--   $$W_3(h)=\big(\mathtt{jacquetWhittaker3}\ p\ \lambda\ \Phi\big)\big(\mathrm{diag}(1,-1,1)\,h\,T\big),$$
--   where `jacquetWhittaker3 p lam Φ` sends $g$ to the value of the functional `jacquetValue` on the right translate by $g$ of the big-cell section `cellSectionOf p lam Φ`, i.e. of the function supported on `bigCell3 p` whose value there is `cellValue p lam · * Φ (cellRatio p ·)`.
--
--   $GL_2$ data: a homomorphism $\theta_0:F^\times\to\mathbb C^\times$; a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$ (`hN`); a function $w_2^{\mathrm{base}}:GL_2(F)\to\mathbb C$ subject to the following hypotheses. `hw₂law`: $w_2^{\mathrm{base}}\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\,g\big)=\psi(x)\,w_2^{\mathrm{base}}(g)$ for all $x\in F$, $g\in GL_2(F)$. `hw₂K`: right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the embedding $GL_2(F)\to GL_2(\mathbb A_{\mathbb Q}^{\mathrm f})$ of the level-$N$ subgroup `AdelicLevel.finiteLevelOne`. `hw₂ne`: $w_2^{\mathrm{base}}\neq 0$. Writing $V$ for the $\mathbb C$-span of the right translates $g\mapsto w_2^{\mathrm{base}}(gh)$, $h\in GL_2(F)$: `hw₂irr` requires that every nonzero $w\in V$ generate $V$, in the sense that $w_2^{\mathrm{base}}$ lies in the span of the right translates of $w$; `hw₂adm` requires that for every open subgroup $U\le GL_2(F)$ there be a finite set $B$ of functions on $GL_2(F)$ such that every $w\in V$ invariant under right translation by $U$ lies in the span of $B$. `hcentral`: $w_2^{\mathrm{base}}(z\cdot 1_2\,g)=\theta_0(z)\,w_2^{\mathrm{base}}(g)$ for $z\in F^\times$. Finally $w_{0,p}\in GL_2(F)$ is an element with underlying matrix $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ (`hw₀p`).
--
--   The conclusion is asserted for every Haar measure $\mu_2$ on $GL_2(F)$ and every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, the subgroup $\{\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right):x\in F\}$ of $GL_2(F)$, and for every $w_2\in V$. Write $\tilde\mu$ for $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of that unipotent subgroup relative to $\mu_{N_2}$, and, for $\delta(g)=\mathrm{mod}(\det g)$,
--   $$\Psi(s;W,F')=\int_{GL_2(F)} W(g)F'(g)\,\delta(g)^{s-1/2}\,d\tilde\mu(g)$$
--   for [`RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom).range μN₂ δ s W F'`](def/LanglandsTunnell_RSCarrier.html#L16), and
--   $$Z(c',\varphi,\chi,s)=\int_{GL_2(F)} c'(g)\,\varphi(g)\,\chi(\det g)\,\mathrm{mod}(\det g)^{s}\,d\mu_2(g)$$
--   for `godementZeta2 p μ₂ c' φ χ s`.
--
--   The assertion is the existence of natural numbers $n$, $n_j$, families $\varphi^{\mathrm{PS}}_i:GL_2(F)\to\mathbb C$, $\varphi_{1,i}:M_2(F)\to\mathbb C$, $\varphi_{2,i}:F\times F\to\mathbb C$ for $i<n$, a family $w_j:GL_2(F)\to\mathbb C$ and a family of $\mathbb C$-linear functionals $\ell_j$ on functions $GL_2(F)\to\mathbb C$ for $j<n_j$, a constant $c\in\mathbb C$ and real abscissae $\sigma_P,\sigma_D$ such that all of the following hold.
--
--   (i) $c\neq 0$. (ii) Each $\varphi^{\mathrm{PS}}_i$ lies in `principalSeries2 p ![lam 1, lam 2]`: it is locally constant, invariant under left translation by $\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)$, and satisfies $\varphi^{\mathrm{PS}}_i(\mathrm{diag}(a_0,a_1)g)=\lambda_1(a_0)\lambda_2(a_1)\sqrt{\|a_0\|/\|a_1\|}\,\varphi^{\mathrm{PS}}_i(g)$. (iii) Each $\varphi_{1,i}$ is locally constant with compact support. (iv) Each $\varphi_{2,i}$ is locally constant with compact support. (v) Each $w_j$ lies in $V$. (vi) Each $\ell_j$ is smooth on $V$: there is an open subgroup $U\le GL_2(F)$ with $\ell_j(v(\cdot\,k))=\ell_j(v)$ for all $k\in U$ and all $v\in V$.
--
--   (vii) (Primal range.) For every $s$ with $\sigma_P<\operatorname{Re}s$: first, $g\mapsto \big(W_3(\iota g)\,w_2(g)\big)\delta(g)^{s-1/2}$ is $\tilde\mu$-integrable, where $\iota=$ `iotaGL` is $g\mapsto\mathrm{diag}(g,1)$; second, for all $i,j$ the function
--   $$g\mapsto\Big(\int_F\psi(x)\,\varphi^{\mathrm{PS}}_i\big(\tilde w\,\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right) g\big)\,dx\Big)\cdot\Big(w_j(g)\,\varphi_{2,i}(g_{10},g_{11})\Big)\cdot\delta(g)^{(s+1/2)-1/2}$$
--   is $\tilde\mu$-integrable, where $\tilde w=$ `antidiagonal2 p` is $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ and $x$ is integrated against `selfDualHaarAt ℚ p`, and the function
--   $$g\mapsto \ell_j\big(x'\mapsto w_2(x'g)\big)\,\varphi_{1,i}(g)\,\lambda_0(\det g)\,\mathrm{mod}(\det g)^{s+1/2}$$
--   is $\mu_2$-integrable; and third, the identity
--   $$\Psi\big(s;\,W_3\circ\iota,\,w_2\big)=c\sum_{i}\sum_{j}\Psi\Big(s+\tfrac12;\,g\mapsto\!\int_F\!\psi(x)\varphi^{\mathrm{PS}}_i(\tilde w\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)g)dx,\ g\mapsto w_j(g)\varphi_{2,i}(g_{10},g_{11})\Big)\cdot Z\big(g\mapsto\ell_j(x'\mapsto w_2(x'g)),\,\varphi_{1,i},\,\lambda_0,\,s+\tfrac12\big).$$
--
--   (viii) (Dual range.) For every $s$ with $\sigma_D<\operatorname{Re}s$, with $g^\star={}^{\mathrm t}(g^{-1})$ (`transposeInvN (Fin 2)`) and with $W_3^{\vee}=$ `dualWhittakerFn3 W₃`, that is $W_3^{\vee}(h)=W_3\big(\left(\begin{smallmatrix}0&0&1\\0&1&0\\1&0&0\end{smallmatrix}\right)\,{}^{\mathrm t}(h^{-1})\big)$: first, $g\mapsto\big(W_3^{\vee}(\iota g)\cdot\mathrm{mod}(\det g)\,w_2(w_{0,p}g^\star)\big)\delta(g)^{s-1/2}$ is $\tilde\mu$-integrable; second, for all $i,j$ the function
--   $$g\mapsto\Big(\int_F\psi(x)\varphi^{\mathrm{PS}}_i\big(\tilde w\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)(w_{0,p}g^\star)\big)dx\Big)\cdot\Big(\mathrm{mod}(\det g)\,w_j(w_{0,p}g^\star)\!\int_{F^2}\!\varphi_{2,i}(u)\psi(u_1g_{10}+u_2g_{11})\,du\Big)\cdot\delta(g)^{(s+1/2)-1/2}$$
--   is $\tilde\mu$-integrable (the inner integral taken against the product of two copies of `selfDualHaarAt ℚ p`), and the function
--   $$g\mapsto \ell_j\big(x'\mapsto w_2(x'g^\star)\big)\cdot\big(\mathtt{matFourier22}\,p\,\psi\,\varphi_{1,i}\big)(g)\cdot\lambda_0^{-1}(\det g)\cdot\mathrm{mod}(\det g)^{s+3/2}$$
--   is $\mu_2$-integrable, where `matFourier22 p ψ` is the composite of the two column-wise Fourier transforms `colFourier22 p ψ 1` and `colFourier22 p ψ 0`, each replacing the indicated column of $X$ by $u\in F^2$ with kernel $\psi(u_1X_{0j}+u_2X_{1j})$; and third, the identity
--   $$\Psi\big(s;\,W_3^{\vee}\circ\iota,\ g\mapsto\mathrm{mod}(\det g)w_2(w_{0,p}g^\star)\big)=c\,\theta_0(-1)\lambda_1(-1)\lambda_2(-1)\sum_i\sum_j\Psi\big(s+\tfrac12;\,W'_{i},\,F'_{i,j}\big)\cdot Z\big(g\mapsto\ell_j(x'\mapsto w_2(x'g^\star)),\ \mathtt{matFourier22}\,p\,\psi\,\varphi_{1,i},\ \lambda_0^{-1},\ s+\tfrac32\big),$$
--   where $W'_i$ and $F'_{i,j}$ are exactly the two factors occurring in the first dual integrability claim above.
--
--   Thus the same constant $c$, the same families and the same abscissae serve both the primal and the dual unfolding, and the dual identity carries the extra scalar $\theta_0(-1)\lambda_1(-1)\lambda_2(-1)$.
--
--   This is the local unfolding identity for the $GL_3\times GL_2$ Rankin–Selberg integral at a finite place, in the mixed (Godement-section) model: the integral of a translated Jacquet–Whittaker function of the principal series $I(\lambda_0,\lambda_1,\lambda_2)$ against a vector of the Whittaker model of a generic representation of $GL_2(F)$ is written, in both the primal and the dual range, as a finite sum of products of a $GL_2\times GL_2$ Rankin–Selberg integral with a Godement–Jacquet zeta integral. It is the common source from which the cleared local functional equation and the rationality statement for the pair are obtained, by inserting the $GL_2\times GL_2$ and Godement–Jacquet functional equations, respectively their rational forms, term by term; the two downstream statements that use it do precisely that.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p)
    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * T))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (n nj : ℕ) (φPS : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₁ : Fin n → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : Fin n → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
            (wj : Fin nj → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (ℓ : Fin nj → (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (σP σD : ℝ),
            c ≠ 0 ∧
            (∀ i, φPS i ∈ principalSeries2 p ![lam 1, lam 2]) ∧
            (∀ i, IsLocallyConstant (φ₁ i) ∧ HasCompactSupport (φ₁ i)) ∧
            (∀ i, IsLocallyConstant (φ₂ i) ∧ HasCompactSupport (φ₂ i)) ∧
            (∀ j, wj j ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) ∧
            (∀ j, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
              ∀ k ∈ U, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓ j (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * k)) = ℓ j v) ∧

            (∀ s : ℂ, σP < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
              (∀ i j, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  wj j g * φ₂ i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * g)) * φ₁ i ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((lam 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (fun g => W₃ (iotaGL g)) w₂ =
                c * ∑ i, ∑ j,
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  wj j g * φ₂ i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
                    godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * g))) (φ₁ i) (lam 0) (s + 1 / 2)) ∧

            (∀ s : ℂ, σD < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
              (∀ i j, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ i u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * transposeInvN (Fin 2) g)) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (φ₁ i) ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  (((lam 0)⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) ∧
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
                c * ((((θ₀ (-1) : ℂˣ) : ℂ) * (((lam 1 (-1) : ℂˣ) : ℂ) * ((lam 2 (-1) : ℂˣ) : ℂ))) *
                  ∑ i, ∑ j,
                    RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ i u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) *
                      godementZeta2 p μ₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * transposeInvN (Fin 2) g)))
                (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (φ₁ i)) (lam 0)⁻¹ (s + 3 / 2))) := by sorry
