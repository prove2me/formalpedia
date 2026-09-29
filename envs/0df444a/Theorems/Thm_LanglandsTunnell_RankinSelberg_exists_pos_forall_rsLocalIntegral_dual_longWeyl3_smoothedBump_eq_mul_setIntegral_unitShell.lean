-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_dual_longWeyl3_smoothedBump_eq_mul_setIntegral_unitShell
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_dual_longWeyl3_smoothedBump_eq_mul_setIntegral_unitShell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/989969ff-f143-5271-bef3-b3855e19a2d3
-- title:
--   Dual Rankin–Selberg integral of a smoothed GL₃ bump vector
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$ and an element $w_{0,p}\in GL_2(\mathbb Q_p)$ whose matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and give $GL_2(\mathbb Q_p)$ and $\mathbb Q_p$ their Borel structures. Write $\psi$ for [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), $\nu$ for `selfDualHaarAt ℚ p`, and $|\cdot|$ for `modulus`. The assertion is: for every Haar measure $\mu_2$ on $GL_2(\mathbb Q_p)$ and every Haar measure $\mu_{N_2}$ on the range of $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$ there is $c>0$, depending only on these data, such that for every character $\omega:\mathbb Q_p^\times\to\mathbb C^\times$, every $f\in\mathbb N$ and every $W_0:GL_3(\mathbb Q_p)\to\mathbb C$ with $W_0(n(x,y,z)g)=\psi^{-1}(x+y)W_0(g)$ for $n(x,y,z)=\begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$, right invariant under some open subgroup, with $W_0(\mathrm{diag}(t,t,t)h)=\omega(t)W_0(h)$, right invariant under the set `congruenceK1 (𝓞 ℚ) ℚ p f` of integral $k$ with $v(k_{20}),v(k_{21}),v(k_{22}-1)\le q^{-f}$, and such that along $\iota(h)=\mathrm{diag}(h,1)$ it is right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), vanishes off the product of the upper unipotent subgroup with that subgroup, and satisfies $W_0(\iota 1)=1$; and for every $w:GL_2(\mathbb Q_p)\to\mathbb C$ and character $\theta$ with $w(\begin{pmatrix}1&x\\0&1\end{pmatrix}g)=\psi(x)w(g)$, $w$ right invariant under some open subgroup and $w(\mathrm{diag}(z,z)g)=\theta(z)w(g)$; and for all Schwartz–Bruhat $\varphi,\varphi_1$ on $\mathbb Q_p$ whose Fourier transforms $\hat{\ }$ taken with respect to $\psi^{-1}$ and $\nu$ satisfy $\hat\varphi(t)=\theta(t)$ for $|t|=1$, $\hat\varphi(y)=0$ for $|y|\ne1$, $\hat\varphi_1(ty)=\omega(t)\hat\varphi_1(y)$ for $|t|=1$, and $\hat\varphi_1(y)\ne0\Rightarrow v(y)\le q^{-f}$: for every $s\in\mathbb C$ the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) formed from $\mu_2$, the unipotent subgroup with $\mu_{N_2}$, the modulus $g\mapsto|\det g|$ and the parameter $s$, taken on the pair consisting of $g\mapsto \widetilde W(\iota g)$, where $\widetilde W(h)=W^{\varphi,\varphi_1}(w_\ell\,{}^t h^{-1})$ and $W^{\varphi,\varphi_1}(x)=\iint W_0(x\,w_\ell\,n(u,0,y))\varphi(u)\varphi_1(y)\,d\nu(y)\,d\nu(u)$ with $w_\ell$ the long Weyl element of $GL_3$, and of $g\mapsto|\det g|\,w(w_{0,p}\,{}^t g^{-1})$, equals $c$ times $\int_{|t|=1}\omega(t)\bigl(\int w(w_{0,p}\,\mathrm{diag}(t,1)\begin{pmatrix}1&x\\0&1\end{pmatrix})\hat\varphi_1(-x)\,d\nu(x)\bigr)$ against the measure on $\mathbb Q_p^\times$ obtained by pulling back $|x|^{-1}\,d\nu$ along $t\mapsto t$.
--
--   This is the local computation of Jacquet–Shalika on highly ramified $\varepsilon$-factors, specialised to $GL_3\times GL_2$ at a finite place: the dual local Rankin–Selberg integral of a smoothed bump Whittaker vector is independent of $s$ and is a fixed positive multiple of an integral over the unit shell of $\mathbb Q_p^\times$. It is used in the construction of test vectors giving equal, explicitly computed, local integrals for the two Whittaker vectors of the cubic-induction frame.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_dual_longWeyl3_smoothedBump_eq_mul_setIntegral_unitShell.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_dual_longWeyl3_smoothedBump_eq_mul_setIntegral_unitShell
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],

      ∃ c : ℝ, 0 < c ∧

        ∀ (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (f : ℕ)

          (W₀ : LocalGL3 p → ℂ),
          IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀ →
          (∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) →
          (∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
            W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h) →
          (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) →
          (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) →
          (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
            ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) →
          W₀ (iotaGL 1) = 1 →

        ∀ (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ),
          (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) →
          (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
          (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
            w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ z : ℂˣ) : ℂ) * w g) →

        ∀ (φ φ₁ : p.adicCompletion ℚ → ℂ), IsSchwartzBruhat φ → IsSchwartzBruhat φ₁ →
          (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ (t : p.adicCompletion ℚ) = ((θ t : ℂˣ) : ℂ)) →
          (∀ y : p.adicCompletion ℚ, Valued.v y ≠ 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ y = 0) →
          (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → ∀ y : p.adicCompletion ℚ,
            tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ ((t : p.adicCompletion ℚ) * y) = ((ω t : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y) →
          (∀ y : p.adicCompletion ℚ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y ≠ 0 → Valued.v y ≤ WithZero.exp (-(f : ℤ))) →
        ∀ s : ℂ,
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s
              (fun g => dualWhittakerFn3
                (fun x : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
                  W₀ (x * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
                (iotaGL g))
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) =
            (c : ℂ) * ∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1},
              ((ω t : ℂˣ) : ℂ) *
                (∫ x : p.adicCompletion ℚ, w (w₀p * diagUnitGL2 t * unipotent x) *
                    tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) ∂(selfDualHaarAt ℚ p))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
