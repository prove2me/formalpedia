-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
-- name    : LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/ef46fbe0-aadf-5cbf-a994-f2c6d3752ff6
-- title:
--   Godement-section realisation of the GL₃ Jacquet–Whittaker function
-- statement:
--   Throughout, $p$ is a nonzero prime of $\mathcal O_{\mathbb Q}$, $F =$ `p.adicCompletion ℚ` the corresponding completion, $\psi =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) the standard additive character of $F$, $dx =$ `selfDualHaarAt ℚ p` the Haar measure on $F$ self-dual for $\psi$, and $|\cdot| =$ `modulus` the Haar module of $F$ (equal to the absolute value $\|\cdot\|$ of $F$). For a homomorphism $\chi : F^\times \to \mathbb C^\times$, `charExt` $\chi$ denotes its extension to $F$ by the value $0$ at $0$. Both $F$ and $GL_2(F)$ carry their Borel $\sigma$-algebras, and $GL_2(F)$ its Borel space structure.
--
--   The data are: a triple $\lambda = (\lambda_0,\lambda_1,\lambda_2)$ of multiplicative homomorphisms $F^\times \to \mathbb C^\times$, the hypothesis `hlam` that each $\lambda_i$ is locally constant, a triple of real exponents $\sigma = (\sigma_0,\sigma_1,\sigma_2)$ together with the hypothesis `hσ` that $\|\lambda_i(a)\| = \|a\|^{\sigma_i}$ for all $a \in F^\times$ and all $i$, the chamber conditions `h01` and `h12` stating $\sigma_1 < \sigma_0$ and $\sigma_2 < \sigma_1$, a function $\Phi : F^3 \to \mathbb C$ with the hypothesis `hΦ` that $\Phi$ is locally constant and has compact support, and an element $T \in GL_3(F)$ (the type `LocalGL3 p`).
--
--   The conclusion asserts the existence of an open set $U \subseteq GL_2(F)$ with $1 \in U$ and of a real number $R$, chosen uniformly in the measure and in the subgroup that follow, such that for every Haar measure $\mu_2$ on $GL_2(F)$, every subgroup $K \le GL_2(F)$ whose underlying set is open and compact, every function $\varphi^{\mathrm{sec}} : M_{2\times 3}(F) \to GL_2(F) \to \mathbb C$ satisfying the defining identity below, and every function $\mathfrak D : M_{2\times 3}(F) \to GL_2(F) \to \mathbb C$ satisfying the second defining identity below, the six assertions (1)–(6) hold.
--
--   The first defining identity requires that for all $X \in M_{2\times 3}(F)$ and $g \in GL_2(F)$, writing $Z = X T$, writing $s$ for the left $2\times 2$ block of $Z$ (columns indexed by `Fin.castSucc`) and $N = g Z$,
--   $$\varphi^{\mathrm{sec}}_X(g) = \frac{\lambda_0(\det T)\,|\det T|}{\mu_2(K)}\; \mathbf 1_{K}(s)\; \lambda_0(\det s)^{-1} \|\det s\|^{-1}\; |\det g|^{1/2}\; \lambda_1\!\Big(\frac{\det g \cdot \det s}{N_{10}}\Big)\, \lambda_2(N_{10})\, \|N_{10}\|^{-1}\, \Phi\!\Big(\frac{N_{11}}{N_{10}}, \frac{N_{12}}{N_{10}}, \frac{Z_{00}Z_{12} - Z_{02}Z_{10}}{\det s}\Big),$$
--   where $\mu_2(K)$ is the real number `(μ₂ K).toReal`, $\mathbf 1_K$ is the indicator function of the image of $K$ in $M_2(F)$ under `Units.val`, the values of $\lambda_0, \lambda_1, \lambda_2$ at possibly zero arguments are taken in the sense of `charExt`, and $\lambda_0(\det T)$, $|\det T|$, $|\det g|^{1/2}$ use the honest values at the units $\det T$, $\det g$. The second defining identity requires that for all $X$ and all $k \in GL_2(F)$,
--   $$\mathfrak D_X(k) = \int_F \psi(x)\, \varphi^{\mathrm{sec}}_X\big(w_2\, n(x)\, k\big)\, dx,$$
--   where $w_2 =$ `antidiagonal2 p` is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(x) =$ `upperUnipotent2 p x` is $\begin{pmatrix}1&x\\0&1\end{pmatrix}$.
--
--   In the statements below, `godementWhittaker3 p ψ⁻¹ μ₂ λ₀ D g` denotes, by definition,
--   $$\lambda_0(\det g)\,|\det g| \int_{GL_2(F)} \big(\mathcal F_3 \,[\,X \mapsto D_{Xg}(h^{-1})\,]\big)\big(\mathrm{ga}(h)\big)\, \lambda_0(\det h)\, |\det h|^{1/2}\, d\mu_2(h),$$
--   where $\mathcal F_3 =$ `rowFourier23 p (ψ⁻¹)⁻¹` is the Fourier transform `colFourier23` in the third-column entries of a $2\times 3$ matrix with respect to the character $(\psi^{-1})^{-1}$, and $\mathrm{ga}(h) =$ `godementArg p h` is the $2\times 3$ matrix whose first two columns are those of $h$ and whose last column is the second column of the transpose-inverse of $h$.
--
--   (1) For every $g \in GL_3(F)$: the function
--   $$h \mapsto \big(\mathcal F_3\,[\,X \mapsto \mathfrak D_{Xg}(h^{-1})\,]\big)(\mathrm{ga}(h))\, \lambda_0(\det h)\, |\det h|^{1/2}$$
--   is $\mu_2$-integrable, that is, the defining integral of `godementWhittaker3` converges, and
--   $$W_{\lambda,\Phi}\big(\mathrm{diag}(1,-1,1)\, g\, T\big) = \lambda_1(-1)\cdot \mathtt{godementWhittaker3}\ p\ \psi^{-1}\ \mu_2\ \lambda_0\ \mathfrak D\ g,$$
--   where $W_{\lambda,\Phi} =$ `jacquetWhittaker3 p lam Φ` is the function on $GL_3(F)$ obtained by applying the Jacquet functional `jacquetValue` to the right translate by the argument of the cell section `cellSectionOf p lam Φ`, and $\mathrm{diag}(1,-1,1) =$ `diagonal3 p ![1, -1, 1]`.
--
--   (2) $\mathfrak D$ has compact support.
--
--   (3) Support in the first variable: for all $X$ and $k$, if $\mathfrak D_X(k) \ne 0$ then the left $2\times 2$ block of $X T$ lies in the image of $K$ under `Units.val`.
--
--   (4) For every $X$: the function $\varphi^{\mathrm{sec}}_X$ lies in `principalSeries2 p ![lam 1, lam 2]`, that is, it is locally constant, invariant under left translation by the upper unipotents $n(x)$, and satisfies $\varphi^{\mathrm{sec}}_X(\mathrm{diag}(a)g) = \mathtt{torusChar2}\,(\lambda_1,\lambda_2)(a)\cdot \mathtt{halfModulus2}(a)\cdot \varphi^{\mathrm{sec}}_X(g)$ for all diagonal $a$; moreover, for every $g$ with $\varphi^{\mathrm{sec}}_X(g) \ne 0$, writing $s$ for the left $2\times 2$ block of $X T$, one has $(g s)_{10} \ne 0$ and $\|(g s)_{11}\| \le R\,\|(g s)_{10}\|$.
--
--   (5) If in addition $K \subseteq U$, then for all $X$ and all $g$ with $\varphi^{\mathrm{sec}}_X(g) \ne 0$ one has $g_{10} \ne 0$ and $\|g_{11}\| \le R\,\|g_{10}\|$.
--
--   (6) A finite pure-tensor decomposition of the datum: there are $m \in \mathbb N$ and families $\varphi_1 : \mathrm{Fin}\,m \to (M_2(F) \to \mathbb C)$, $\varphi_2 : \mathrm{Fin}\,m \to (F \times F \to \mathbb C)$ and $\varphi : \mathrm{Fin}\,m \to (GL_2(F) \to \mathbb C)$ such that each $\varphi_1(i)$ is locally constant with compact support, each $\varphi_2(i)$ is locally constant with compact support, each $\varphi(i)$ lies in `principalSeries2 p ![lam 1, lam 2]` and admits some $s \in K$ with $(g s)_{10} \ne 0$ for every $g$ with $\varphi(i)(g) \ne 0$; such that for all $X$ and $k$
--   $$\mathfrak D_X(k) = \sum_{i} \varphi_1(i)\big(\text{left } 2\times 2 \text{ block of } X\big)\, \varphi_2(i)\big(X_{02}, X_{12}\big) \int_F \psi(x)\, \varphi(i)\big(w_2\, n(x)\, k\big)\, dx;$$
--   and such that for every $g \in GL_3(F)$, denoting by $\mathfrak D^{(i)}$ the $i$-th summand above regarded as a function of $(X,k)$, each of the $m$ Godement integrands
--   $$h \mapsto \big(\mathcal F_3\,[\,X \mapsto \mathfrak D^{(i)}_{Xg}(h^{-1})\,]\big)(\mathrm{ga}(h))\, \lambda_0(\det h)\, |\det h|^{1/2}$$
--   is $\mu_2$-integrable and
--   $$W_{\lambda,\Phi}\big(\mathrm{diag}(1,-1,1)\, g\, T\big) = \lambda_1(-1) \sum_{i} \mathtt{godementWhittaker3}\ p\ \psi^{-1}\ \mu_2\ \lambda_0\ \mathfrak D^{(i)}\ g.$$
--   Note that in the decomposition $\varphi_1(i)$ is evaluated at the left $2\times 2$ block of $X$ itself and $\varphi_2(i)$ at its last column, whereas the twist by $T$ is built into $\varphi^{\mathrm{sec}}$.
--
--   This is the local Godement-section realisation of the Jacquet–Whittaker function of a $GL_3$ principal series: the translate $W_{\lambda,\Phi}(\mathrm{diag}(1,-1,1)\,g\,T)$ is identified, up to the constant $\lambda_1(-1)$, with the mixed-model ($GL_2$-slot Whittaker, $GL_3$-slot Fourier) Whittaker function of an explicit Godement datum $\mathfrak D$, together with the support, principal-series and pure-tensor properties of that datum needed downstream. It feeds the local Rankin–Selberg computation in the Langlands–Tunnell input, being used by [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

    ∃ (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) (R : ℝ), IsOpen U ∧ (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U ∧
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →

    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →

    ∀ (𝔇 : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (𝔇 = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
        ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          φsec X (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) →

    (∀ g : LocalGL3 p,
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          rowFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹⁻¹
              (fun X => 𝔇 (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
              (godementArg p h) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ)) μ₂ ∧
      jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * g * T) =
        ((lam 1 (-1) : ℂˣ) : ℂ) *
          godementWhittaker3 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ μ₂ (lam 0) 𝔇 g) ∧

    HasCompactSupport 𝔇 ∧
    (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), 𝔇 X k ≠ 0 →
      (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j)) ∈
        Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))) ∧

    (∀ X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ),
      φsec X ∈ principalSeries2 p ![lam 1, lam 2] ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φsec X g ≠ 0 →
        ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0 ≠ 0 ∧
        ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 1‖ ≤
          R * ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0‖) ∧

    ((K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ⊆ U →
      ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), φsec X g ≠ 0 →
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0 ∧
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ≤
            R * ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖) ∧

    (∃ (m : ℕ) (φ₁ : Fin m → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
        (φ₂ : Fin m → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
        (φ : Fin m → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ i, IsLocallyConstant (φ₁ i) ∧ HasCompactSupport (φ₁ i)) ∧
      (∀ i, IsLocallyConstant (φ₂ i) ∧ HasCompactSupport (φ₂ i)) ∧
      (∀ i, φ i ∈ principalSeries2 p ![lam 1, lam 2] ∧
        ∃ s ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ i g ≠ 0 →
          ((g * s : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0) ∧
      (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        𝔇 X k = ∑ i, φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
          ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) ∧

      ∀ g : LocalGL3 p,
        (∀ i, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            rowFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹⁻¹
                (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
                  (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
                (godementArg p h) *
              ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
                ^ (1 / 2 : ℂ)) μ₂) ∧
        jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * g * T) =
          ((lam 1 (-1) : ℂˣ) : ℂ) *
            ∑ i, godementWhittaker3 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ μ₂ (lam 0)
              (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) g) := by sorry
