-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous
-- name    : LanglandsTunnell.CubicInduction.integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/1c2d7a5e-57b2-5d74-bfbb-673e5b6ed98f
-- title:
--   Jacquet unfolding of a Godement section on GL₃
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, a continuous additive character $\eta$ of the completion $F=\mathbb{Q}_p$ with values in $\mathbb{C}$, a homomorphism $\lambda_0\colon F^\times\to\mathbb{C}^\times$, a function $D\colon M_{2\times 3}(F)\times GL_2(F)\to\mathbb{C}$, written $D(X)(k)$, and a function $F_{\mathrm{sec}}\colon GL_3(F)\to\mathbb{C}$; all spaces carry their Borel $\sigma$-algebras. Let $\mu_2$ be a Haar measure on $GL_2(F)$, and write $|a|$ for `modulus` $a$, equal to $\|a\|$ by [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm), and $(h\,|\,0)$ for the $2\times 3$ matrix with first two columns $h$ and last column $0$. Assume: (i) $F_{\mathrm{sec}}(Y)=\lambda_0(\det Y)\,|\det Y|\int_{GL_2(F)} D\bigl((h\,|\,0)\,Y\bigr)(h^{-1})\,\lambda_0(\det h)\,|\det h|^{3/2}\,d\mu_2(h)$ for every $Y\in GL_3(F)$; (ii) $(X,k)\mapsto D(X)(k)$ is measurable on the product; and, for a fixed $g\in GL_3(F)$, (iii) the function $((x,y,z),h)\mapsto D\bigl((h\,|\,0)\,n(x,y,z)g\bigr)(h^{-1})\,\lambda_0(\det h)\,|\det h|^{3/2}$ is integrable for `jacquetHaar3` $\otimes\,\mu_2$, where $n(x,y,z)=\left(\begin{smallmatrix}1&x&z\\0&1&y\\0&0&1\end{smallmatrix}\right)$ and `jacquetHaar3` is the threefold product of the self-dual Haar measure $dx$ on $F$. Set $D^{W}(X)(k)=\int_F \eta^{-1}(x)\,D(X)\bigl(n_2(x)k\bigr)\,dx$ with $n_2(x)=\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)$. The conclusion is twofold: the function $h\mapsto \bigl(\mathrm{rowFourier23}\,\eta^{-1}\bigr)\bigl(X\mapsto D^{W}(Xg)(h^{-1})\bigr)\bigl(\mathrm{godementArg}\,h\bigr)\lambda_0(\det h)|\det h|^{1/2}$ is $\mu_2$-integrable, and $$\int_{F^3}\eta^{-1}(x+y)\,F_{\mathrm{sec}}\bigl(n(x,y,z)g\bigr)\,dx\,dy\,dz=\mathrm{godementWhittaker3}\;\eta\;\mu_2\;\lambda_0\;D^{W}\;g,$$ the right-hand side being $\lambda_0(\det g)|\det g|$ times the $\mu_2$-integral just described; here `rowFourier23` is the Fourier transform of the last column, $\Phi\mapsto\int_{F^2}\Phi(\mathrm{setCol23}\,X\,2\,u)\,\eta^{-1}(u_1X_{02}+u_2X_{12})\,du$, and $\mathrm{godementArg}\,h$ is the $2\times 3$ matrix with first two columns $h$ and last column the second column of ${}^{t}h^{-1}$.
--
--   This is the local unfolding computation identifying the Jacquet integral of a Godement section on $GL_3(\mathbb{Q}_p)$ with the mixed-model Whittaker function attached to the slot-wise Whittaker transform of its datum, in the shape used in Rankin–Selberg theory for $GL_3\times GL_2$. It feeds the evaluation of the Jacquet–Whittaker generator on diagonal elements in [`LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber`](thm.html#LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous.lean

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

theorem LanglandsTunnell.CubicInduction.integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous
    (p : HeightOneSpectrum (𝓞 ℚ))
    (η : AddChar (p.adicCompletion ℚ) ℂ) (hη : Continuous η)
    (lam0 : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (D : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (Fsec : LocalGL3 p → ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],

      (∀ Y : LocalGL3 p, Fsec Y = ((lam0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            D ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹ *
              ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ) ∂μ₂) →

      Measurable (fun P : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => D P.1 P.2) →
      ∀ g : LocalGL3 p,

      Integrable (fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          D ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((r.2 : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) *
                ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) r.2⁻¹ *
            ((lam0 (Matrix.GeneralLinearGroup.det r.2) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det r.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ))
        ((jacquetHaar3 p).prod μ₂) →
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          rowFourier23 p η⁻¹
              (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
                  ∫ x : p.adicCompletion ℚ, η⁻¹ x * D X (upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
                (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
              (godementArg p h) *
            ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) μ₂ ∧
      ∫ q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
          η⁻¹ (q.1 + q.2.1) * Fsec (upperUnipotent3 q.1 q.2.1 q.2.2 * g) ∂(jacquetHaar3 p) =
        godementWhittaker3 p η μ₂ lam0
          (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
            ∫ x : p.adicCompletion ℚ, η⁻¹ x * D X (upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) g := by sorry
