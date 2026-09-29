-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight
-- name    : LanglandsTunnell.exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/685045a1-5278-58c6-98c1-e507bd136e65
-- title:
--   Whittaker factorisation for a minimal-weight Casimir eigenvector
-- statement:
--   Work over $\mathbb{Q}$ with real parameters $c,u,d_1,d_2$, a finite set $T$ of adelic $\mathrm{GL}_2$-elements, and $D=\bigcup_{x\in T}(\,\cdot\,x)(\text{centreCutSiegelSet }\mathbb{Q}\,c\,u\,d_1\,d_2)$, assumed to cover $\mathrm{GL}_2(\mathbb{A})$ modulo left $\mathrm{GL}_2(\mathbb{Q})$-translation and the centre; $d_1<d_2$ is assumed. Throughout, the carrier data are the production pins on $D$ with level subgroups `levelOne` intersected with the kernel of the archimedean projection, Hecke generators `heckeGen` and averaging box `adelicBox`. Given a Hecke eigensystem $\Phi$ over $\mathbb{Q}$, a smooth cusp realisation $R$ of `Φ.toRawCentral` (the eigensystem with $b_v$ rescaled by $(\mathrm{Nm}\,v)^{-1}$) with continuous underlying function, a global additive character $\psi$ (trivial on $\mathbb{Q}$, continuous, non-trivial) whose component at each real place is $x\mapsto e^{2\pi i x}$, a finite set $S$ of finite places containing `R.exceptionalSet`, and for each real place $w$ an archimedean parameter $\mathrm{archR}\,w$: the hypotheses are that principal parameters satisfy $|\mathrm{Re}(u_1-u_2)|<1$; that the central character of $R$ has local component $x\mapsto\|x\|^{\mathrm{mult}_w\cdot(\text{centralExponent}+1)}(x/\|x\|)^{\text{centralSign}}$ at $w$; and that $\varphi_1$ is a non-zero isotypic cusp form for these pins with central character `R.centralChar`, level $\Phi.\mathrm{level}$, Hecke eigenvalues $\Phi.a_v$ away from $S$, equal to its right convolution with some factorisable test function, transforming by the weight-$k_1(w)$ character `archWeightCharAt` at each real place, with $k_1(w)\in\{0,1\}$ and $k_1(w)\equiv a_1+a_2 \pmod 2$ for principal parameters and $k_1(w)=n+1$ for discrete ones, archimedean-smooth at each real place with Casimir eigenvalue the Laplace eigenvalue of $\mathrm{archR}\,w$, satisfying $\varphi_1(g\cdot J_w)=(-1)^{a_1}\varphi_1(g)$ when $\mathrm{archR}\,w$ is principal with $a_1=a_2$, and annihilated by $H-i(E+F^-)$ when $\mathrm{archR}\,w$ is discrete or principal with equal exponents and $a_1\neq a_2$; finally every principal parameter has $a_1=a_2$ or $u_1=u_2$. The conclusion asserts the existence of a single function $C$ of a finite idele and a group element such that for every parity vector $\mathrm{par}:\text{places}\to\mathbb{Z}/2$ there are $\varphi$, real-place profiles $W_w:\mathbb{C}\to\mathbb{C}$ and weights $k$ with: $\varphi$ a non-zero isotypic cusp form for the same data, equal to its right convolution with a factorisable test function, of archimedean weight $k(w)$, where $k(w)=\mathrm{signShift}(a_1+\mathrm{par}\,w)+\mathrm{signShift}(a_2+\mathrm{par}\,w)$ for principal parameters and $k(w)=n+1$ for discrete ones; the Whittaker coefficient of $\varphi$ at $\alpha=1$ factorises as $\prod_w W_w$ of the embedded infinite components times $C$ of the finite component, evaluated at $\mathrm{diagOne}(a)\,g$ for every idele $a$ and every $g$ with trivial archimedean component; $W_w(-t)=(-1)^{a_1}W_w(t)$ when $\mathrm{archR}\,w$ is principal with $a_1=a_2$ and $\mathrm{par}\,w=a_1$; $W_w$ vanishes on the negative reals for discrete parameters; in the principal case with $a_1=a_2$ and $\mathrm{par}\,w=a_1+1$ the Mellin transform of $t\mapsto (W_w(t)+(-1)^{a_1}W_w(-t))/t$ converges in a right half-plane and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of the $(0,a_1)$-twist of $\mathrm{archR}\,w$; and for each $b$ equal to $\mathrm{par}\,w$ or to $\mathrm{par}\,w+\text{centralSign}(\mathrm{archR}\,w)$ the corresponding Mellin transform equals the archimedean factor of the $(0,b)$-twist.
--
--   This is the archimedean input to the converse-theorem step of the Langlands–Tunnell argument: starting from a minimal-weight Casimir eigenvector in an isotypic cusp space, it produces for each choice of parity a member of the associated weight family whose first Whittaker coefficient splits as a product of real-place profiles times a function of the finite data, with the profiles' Mellin transforms given by the expected archimedean $\Gamma$-factors. It is used in the construction of the twisted weight-one constituent whose Whittaker coefficients agree with a prescribed archimedean profile away from finitely many places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem LanglandsTunnell.exists_whittaker_factorization_of_archCasimir_eigenvector_minimalWeight
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂)
    (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (_hR : Continuous R.toFun)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g)
    (_hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
        archDerivAt hw ArchDir.H φ₁
            - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0)
    (_heq : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂) :
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
    ∀ par : InfinitePlace ℚ → ZMod 2,
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
        IsIsotypicCuspFormAt ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
              (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
              (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
            whittakerCoefficient ℚ
                (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                  (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                  (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
                ψ φ 1 (diagOne a * g)
              = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                  * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
            ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                  = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                      * ((archR w hw).twist 0 a₁).archFactor s) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
          (b = par w ∨ b = par w + (archR w hw).centralSign) →
            ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
              MellinConvergent
                  (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                  = ((archR w hw).twist 0 b).archFactor s) := by sorry
