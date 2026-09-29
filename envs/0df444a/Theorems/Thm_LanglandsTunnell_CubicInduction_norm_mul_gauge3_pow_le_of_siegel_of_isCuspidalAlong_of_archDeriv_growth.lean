-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
-- name    : LanglandsTunnell.CubicInduction.norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/d044d3b7-4788-5882-ab35-6a752a16999d
-- title:
--   Rapid decay on Siegel sets for GL₃ cusp forms
-- statement:
--   Let $\varphi:\mathrm{GL}_3(\mathbb A_{\mathbb Q})\to\mathbb C$ be continuous and invariant under left translation by the image of $\mathrm{GL}_3(\mathbb Q)$ under `globalPointsGL`. Assume $\varphi$ is cuspidal along both maximal parabolics in the sense of `IsCuspidalAlongP21` and `IsCuspidalAlongP12` for the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, i.e. for every $g$ the iterated integral of $\varphi(\mathrm{radical}(x,y)\,g)$ over the two variables vanishes, the measure being the adelic additive Haar measure conditioned on the box (infinite box times integral finite adeles). Assume: for all $p$ outside a finite set $S$, $\varphi$ is right invariant under the image of `localMaximalCompact3` (matrices whose entries and whose inverse's entries have valuation $\le 1$); at every finite place some open subgroup of $\mathrm{GL}_3(\mathbb Q_v)$ fixes $\varphi$ on the right; $\varphi$ is `IsArchSmooth3`, i.e. $e\mapsto\varphi(g\cdot\mathrm{archRealLift3}\,e)$ is smooth on invertible real $3\times 3$ matrices for each $g$; every iterated `archDeriv` word (derivative at $s=0$ along $1+sE_{ij}$ at infinity) is continuous; and, for a fixed $N\in\mathbb N$, every such word satisfies $\|\partial_w\varphi(g)\|\le C_w\,\mathrm{gauge3}(g)^N$, where $\mathrm{gauge3}(g)=\max(1,\mathrm{archGauge3}(g)\,\mathrm{finGauge3}(g))$. Let $c,C,a,b$ be reals with $c>0$ and $0<a<b$. Then for every $M\in\mathbb N$ there is $C'$ such that $\|\varphi(ntk)\|\cdot\mathrm{gauge3}(ntk)^M\le C'$ whenever $n,t,k\in\mathrm{GL}_3(\mathbb A_{\mathbb Q})$ satisfy: all finite components of $n$ and of $t$ are $1$; every finite component of $k$ lies in `localMaximalCompact3`; at each infinite place $w$, the component of $n$ has diagonal entries $1$, vanishing entries strictly below the diagonal and all entries of norm $\le C$, the component of $t$ is diagonal, the quantities `archRoot₁ ℚ w t` and `archRoot₂ ℚ w t` attached to $t$ are both $\ge c$, and the component of $k$ is orthogonal ($k^{\mathsf T}k=1$); and the idele norm of $\det(ntk)$, defined by the module of the distributive Haar character, lies in $[a,b]$.
--
--   This is the rapid-decay statement for cusp forms of uniform moderate growth on Siegel sets in $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$: cuspidality along the two maximal parabolics upgrades a polynomial bound in the gauge to decay faster than any power of it, uniformly on a Siegel set cut out by the determinant slab $a\le\|\det\|\le b$. It feeds the bound for the smoothing operator on such a slab, the $L^2$ estimate for the torus integral of the associated Whittaker function, and the verification that the relevant functions belong to the space of cusp functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) φ)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) φ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ (g * localToAdelic3 v k) = φ g)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hcw : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w))
    (N : ℕ) (hgr : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w g‖ ≤ C * gauge3 ℚ g ^ N)
    (c C a b : ℝ) (hc0 : 0 < c) (ha : 0 < a) (hab : a < b) :
    ∀ M : ℕ, ∃ C' : ℝ, ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
        (∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) →
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) ∈ Set.Icc a b →
        ‖φ (n * t * k)‖ * gauge3 ℚ (n * t * k) ^ M ≤ C' := by sorry
