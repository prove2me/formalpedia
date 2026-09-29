-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isGaugeMajorised3_hasIotaMoments_hasWhittakerHalfPlane_comp_mul_right
-- name    : LanglandsTunnell.CubicInduction.isGaugeMajorised3_hasIotaMoments_hasWhittakerHalfPlane_comp_mul_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/1819c296-df10-5704-822a-a8de57ef1f95
-- title:
--   Right translation stability of cubic-induction Whittaker data
-- statement:
--   Let $\Phi, W, W'$ be complex-valued functions on $GL_3$ of the adeles of $\mathbb{Q}$, with $W$ and $W'$ continuous and both gauge-majorised in the sense of `IsGaugeMajorised3`: there are $t \in \mathbb{N}$, a finite set $T$ of finite places and $B \in \mathbb{R}$ such that the function vanishes off the locus `InRootLevel` determined by $T,B$, and on that locus, for every $N$, is bounded by $C/(\mathrm{rootSizeProd}^{\,t}(1+\mathrm{archRootSum})^N)$ for some $C$. Assume further that for every $g$ the family $i \mapsto W(\mathrm{mirabolicTranslate}(i) \cdot g)$, indexed by the right cosets `MirabolicIndex` of the image of the unipotent homomorphism in $GL_2(\mathbb{Q})$ and translated by the images of coset representatives under $GL_2 \hookrightarrow GL_3$, has sum $\Phi(g)$, and likewise that $i \mapsto W'(\mathrm{mirabolicTranslate}(i) \cdot g)$ has sum $(\mathrm{dualForm}\,\Phi)(g) = \Phi({}^t g^{-1})$. Then for every $k \in GL_3(\mathbb{A}_\mathbb{Q})$ the following hold simultaneously: the dual of $x \mapsto \Phi(xk)$ is $x \mapsto (\mathrm{dualForm}\,\Phi)(x \cdot {}^t k^{-1})$; for all `CarrierPins` data, every additive character $\psi$ of the adeles and every $x$, the triple unipotent integral `whittaker3` of the translate at $\psi$ equals that of $\Phi$ at $xk$, and the $\psi^{-1}$-integral of the dual of the translate equals that of $\mathrm{dualForm}\,\Phi$ at $x\,{}^tk^{-1}$; $x \mapsto W(xk)$ and $x \mapsto W'(x\,{}^tk^{-1})$ are continuous and gauge-majorised, and continuity of $\Phi$ passes to $x \mapsto \Phi(xk)$; the mirabolic expansions hold in translated form, summing to $\Phi(gk)$ and to the dual of the translate at $g$; both $x \mapsto \Phi(xk)$ and its dual satisfy `HasIotaMoments` (finiteness of the weighted integrals over a fundamental domain for the rational points in $GL_2(\mathbb{A})$ with determinant-norm weights $\mathrm{detNorm}^{\pm N}$); and $x \mapsto W(xk)$ and $x \mapsto W'(x\,{}^tk^{-1})$ satisfy `HasWhittakerHalfPlane` (finiteness, for all $\sigma$ beyond some $\sigma_0$, of the integral over such a domain of the mirabolic sum of norms weighted by $\mathrm{detNorm}^\sigma$).
--
--   This packages the stability of the full set of analytic hypotheses attached to a cubic-induction Whittaker datum on $GL_3$ under an arbitrary right translation, with no support or normaliser restriction on the translating element, and records how the Whittaker coefficient and the dual function transform. It is used in the Rankin–Selberg stage of the Langlands–Tunnell construction, where translates of a fixed Whittaker function must be fed back into the same growth and integrability framework.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isGaugeMajorised3_hasIotaMoments_hasWhittakerHalfPlane_comp_mul_right.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.isGaugeMajorised3_hasIotaMoments_hasWhittakerHalfPlane_comp_mul_right
    (Φ W W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hWc : Continuous W) (hW : IsGaugeMajorised3 ℚ W)
    (hW'c : Continuous W') (hW' : IsGaugeMajorised3 ℚ W')
    (hΦ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Φ g))
    (hΦ' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Φ g))
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) :

    (dualForm (fun x => Φ (x * k)) = fun x => dualForm Φ (x * transposeInv3 k)) ∧
    (∀ (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ),
      whittaker3 pins ψ (fun y => Φ (y * k)) x = whittaker3 pins ψ Φ (x * k)) ∧
    (∀ (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ),
      whittaker3 pins ψ⁻¹ (dualForm fun y => Φ (y * k)) x = whittaker3 pins ψ⁻¹ (dualForm Φ) (x * transposeInv3 k)) ∧

    Continuous (fun x => W (x * k)) ∧ Continuous (fun x => W' (x * transposeInv3 k)) ∧
    (Continuous Φ → Continuous fun x => Φ (x * k)) ∧

    IsGaugeMajorised3 ℚ (fun x => W (x * k)) ∧ IsGaugeMajorised3 ℚ (fun x => W' (x * transposeInv3 k)) ∧

    (∀ g, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * (g * k))) (Φ (g * k))) ∧
    (∀ g, HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * (g * transposeInv3 k)))
      (dualForm (fun x => Φ (x * k)) g)) ∧

    HasIotaMoments (fun x => Φ (x * k)) ∧ HasIotaMoments (dualForm fun x => Φ (x * k)) ∧

    HasWhittakerHalfPlane (fun x => W (x * k)) ∧ HasWhittakerHalfPlane (fun x => W' (x * transposeInv3 k)) := by sorry
