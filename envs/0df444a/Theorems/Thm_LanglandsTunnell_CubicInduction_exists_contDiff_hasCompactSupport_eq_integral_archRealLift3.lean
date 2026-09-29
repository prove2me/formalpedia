-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_contDiff_hasCompactSupport_eq_integral_archRealLift3
-- name    : LanglandsTunnell.CubicInduction.exists_contDiff_hasCompactSupport_eq_integral_archRealLift3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/228b53ce-c35a-55dc-8b0c-a9aae07c27cc
-- title:
--   Reproducing identity at the infinite place on GL₃
-- statement:
--   Let $\varphi \colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be a function on the group of invertible $3\times 3$ matrices over the adele ring of $\mathbb{Q}$, subject to three hypotheses. First, [`WhittakerBlock.IsArchSmooth3 φ`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21): for every $g$, the function $e \mapsto \varphi(g \cdot \mathrm{archRealLift3}(e))$ on real $3\times 3$ arrays is $C^\infty$ on the set $\{e : \det(e) \neq 0\}$, where $\mathrm{archRealLift3}(e)$ is the adelic matrix obtained by placing the real matrix $e$ at the archimedean place and the identity at the finite places, taken as a unit of the matrix ring when it is one and as $1$ otherwise. Secondly, there is a finite set $s$ of complex-valued functions on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ such that for every $k$ whose component at each height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ is the identity and whose archimedean component $k_\infty$ satisfies $k_\infty^{\mathsf{T}} k_\infty = 1$ over the infinite adeles, the right translate $g \mapsto \varphi(gk)$ lies in the $\mathbb{C}$-span of $s$. Thirdly, `IsCentreFinite φ`: each of the three operators $\mathrm{casimir1}\,\psi = \sum_i \mathrm{archDeriv}\,i\,i\,\psi$, $\mathrm{casimir2}\,\psi = \sum_{i,j} \mathrm{archDeriv}\,i\,j(\mathrm{archDeriv}\,j\,i\,\psi)$ and $\mathrm{casimir3}\,\psi = \sum_{i,j,k} \mathrm{archDeriv}\,i\,j(\mathrm{archDeriv}\,j\,k(\mathrm{archDeriv}\,k\,i\,\psi))$ annihilates $\varphi$ after a monic linear relation among its iterates: there are $N$ and coefficients $a \colon \mathrm{Fin}(N+1) \to \mathbb{C}$ with $a(N) = 1$ and $\sum_m a(m)\, \mathrm{casimir}^{[m]}\varphi = 0$. The conclusion is that there exists $\alpha \colon (\mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}) \to \mathbb{C}$ which is $C^\infty$, has compact support, has topological support contained in $\{e : \det(e) \neq 0\}$, and satisfies $\varphi(g) = \int \varphi(g \cdot \mathrm{archRealLift3}(h))\,\alpha(h)\,dh$ for every $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, the integral being over all real $3 \times 3$ arrays.
--
--   This is the statement that a smooth, orthogonally finite and centre-finite function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ is reproduced by convolution at the archimedean place against a single smooth compactly supported kernel supported in the invertible arrays, the standard mechanism by which elliptic regularity and $K$-finiteness replace an approximate identity by an exact one. It is used in the cubic-induction part of the Langlands–Tunnell input, where it feeds the estimates on iterated archimedean derivatives of translates and the non-vanishing statement for sums of translates governing the Whittaker block.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_contDiff_hasCompactSupport_eq_integral_archRealLift3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

theorem
LanglandsTunnell.CubicInduction.exists_contDiff_hasCompactSupport_eq_integral_archRealLift3
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => φ (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (hz : IsCentreFinite φ) :
    ∃ α : (Fin 3 → Fin 3 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) α ∧ HasCompactSupport α ∧
      tsupport α ⊆ {e | (Matrix.of e).det ≠ 0} ∧
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g = ∫ h : Fin 3 → Fin 3 → ℝ, φ (g * WhittakerBlock.archRealLift3 h) * α h := by sorry
