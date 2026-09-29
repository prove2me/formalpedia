-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_norm_le_of_isCuspidalAlong_of_arch_oscillation_le
-- name    : LanglandsTunnell.CubicInduction.norm_le_of_isCuspidalAlong_of_arch_oscillation_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f3190a31-2a29-50ad-9334-b1ecc8c57b19
-- title:
--   Oscillation bound for cuspidal functions on GL₃(A_ℚ)
-- statement:
--   Let $m$ be a nonzero element of $\mathcal{O}_{\mathbb{Q}}$ and let $\Phi\colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be continuous, invariant under left translation by the image of $\mathrm{GL}_3(\mathbb{Q})$, and satisfying `IsCuspidalAlongP21` and `IsCuspidalAlongP12` for the carrier data with empty region, trivial level subgroups and unit generators, and with the adelic box $\{x : x_\infty\in\text{infiniteBox},\ x_{\mathrm{f}}\ \text{integral}\}$ as conditioning set: that is, for every $h$ the iterated integral of $\Phi(u\,h)$ over the additive adelic Haar measure conditioned on that box vanishes, where $u$ runs over the unipotent matrices $!![1,0,x;0,1,y;0,0,1]$, respectively $!![1,x,y;0,1,0;0,0,1]$. Assume further that $\Phi$ is invariant under right translation by the adelic image (trivial at the archimedean places) of any finite-adelic $k$ whose component at each height-one prime $p$ has all entries of $k$ and $k^{-1}$ of valuation $\le 1$ and all entries of $k-1$ of valuation $\le |m|_p$. Let $g$ have all its finite components with entries of the matrix and its inverse of valuation $\le 1$, and let $R$ be real. Then two implications hold: if $\|\Phi(g)-\Phi(u\,g)\|\le R$ for all purely archimedean unipotent translates $u$ built as above from $x_\infty,y_\infty$ with $m^{-1}x$, $m^{-1}y$ in the box, then $\|\Phi(g)\|\le R$; and likewise for the second family of unipotents.
--
--   This is the oscillation step in the classical argument that cusp forms are rapidly decreasing on Siegel sets: vanishing of the constant term along the unipotent radical of a maximal parabolic turns the value at an integral point into an average of differences $\Phi(g)-\Phi(ug)$ over a scaled box, with no Fourier expansion required. It feeds the uniform growth estimate [`LanglandsTunnell.CubicInduction.norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth`](thm.html#LanglandsTunnell.CubicInduction.norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_norm_le_of_isCuspidalAlong_of_arch_oscillation_le.lean

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
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.norm_le_of_isCuspidalAlong_of_arch_oscillation_le
    (m : 𝓞 ℚ) (hm : m ≠ 0)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous Φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) Φ)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) Φ)
    (hinv : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      (∀ p : HeightOneSpectrum (𝓞 ℚ),
        componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
          ∀ i j, Valued.v (((componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) :
            Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) i j) ≤
            Valued.v (algebraMap ℚ (p.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ m))) →
      Φ (x * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = Φ x)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (R : ℝ) :
    ((∀ x y : AdeleRing (𝓞 ℚ) ℚ,
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ m)⁻¹ * x ∈ AdelicBox.adelicBox ℚ →
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ m)⁻¹ * y ∈ AdelicBox.adelicBox ℚ →
        ‖Φ g - Φ (radicalP21 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) * g)‖ ≤ R) →
      ‖Φ g‖ ≤ R) ∧
    ((∀ x y : AdeleRing (𝓞 ℚ) ℚ,
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ m)⁻¹ * x ∈ AdelicBox.adelicBox ℚ →
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ m)⁻¹ * y ∈ AdelicBox.adelicBox ℚ →
        ‖Φ g - Φ (radicalP12 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) * g)‖ ≤ R) →
      ‖Φ g‖ ≤ R) := by sorry
