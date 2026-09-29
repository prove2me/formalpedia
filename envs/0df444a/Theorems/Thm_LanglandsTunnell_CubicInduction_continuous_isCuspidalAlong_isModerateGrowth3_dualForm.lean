-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm
-- name    : LanglandsTunnell.CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/0e369586-a015-531e-8dda-435a33eab362
-- title:
--   Transpose-inverse dual of a GL₃ cusp form
-- statement:
--   Fix a set $D$ of adelic $\mathrm{GL}_2$-points over $\mathbb{Q}$, a family $U$ of subgroups of $\mathrm{GL}_2$ of the adeles indexed by ideals of $\mathbb{Z}$, a choice $\mathrm{gen}$ of an adelic $\mathrm{GL}_2$-element for each height-one prime, a character $\omega\colon (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$, and a function $\Phi$ on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$ with values in $\mathbb{C}$. Assume: $\Phi$ is continuous; $\Phi(\gamma g)=\Phi(g)$ for every $\gamma \in \mathrm{GL}_3(\mathbb{Q})$, embedded adelically by `globalPointsGL`, and every adelic $g$; $\Phi(z g)=\omega(z)\,\Phi(g)$ for every idelic scalar $z$ acting through `centralScalarGL`; $\Phi$ is cuspidal along both radicals, i.e. for all $g$ the iterated integrals $\int\!\int \Phi(\mathrm{upperUnipotent3}\,0\,y\,x \cdot g)$ and $\int\!\int \Phi(\mathrm{upperUnipotent3}\,x\,0\,y \cdot g)$ vanish, the integrals being taken against the additive adelic Haar measure conditioned on the adelic box (infinite box times integral finite adeles), which is the measure component of `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`; and $\Phi$ is of moderate growth, i.e. $\|\Phi(g)\| \le C\,\mathrm{gauge3}(g)^N$ for some $C$ and $N$ and all $g$. Then the dual $\mathrm{dualForm}\,\Phi\colon g \mapsto \Phi({}^{t}g^{-1})$ satisfies the same six conditions, with the central character replaced by $\omega^{-1}$.
--
--   This is the statement that the contragredient, or transpose-inverse dual, of a cusp form on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$ is again a cusp form, with the inverse central character; the two cuspidality conditions refer to the unipotent radicals of the two maximal parabolics, and only the measure datum of the carrier pins enters them. It is used in the cubic induction part of the Langlands–Tunnell argument, where it supports the construction of cubic induction data and the transport of ray-order conditions along `transposeInv3`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hc : Continuous Φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * Φ g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hmg : IsModerateGrowth3 ℚ Φ) :
    Continuous (dualForm Φ) ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), dualForm Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = dualForm Φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        dualForm Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ)⁻¹ * dualForm Φ g) ∧
      IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (dualForm Φ) ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (dualForm Φ) ∧
      IsModerateGrowth3 ℚ (dualForm Φ) := by sorry
