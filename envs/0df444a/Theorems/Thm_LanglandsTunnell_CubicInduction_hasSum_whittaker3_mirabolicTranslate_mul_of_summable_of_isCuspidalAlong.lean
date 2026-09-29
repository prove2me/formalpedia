-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong
-- name    : LanglandsTunnell.CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b66e8252-f3b0-5330-925d-3794d102ddb9
-- title:
--   Mirabolic Whittaker expansion of a cuspidal GL₃ form over ℚ
-- statement:
--   Fix a set $D$ of adelic points of $\mathrm{GL}_2$ over $\mathbb{Q}$, an assignment $U$ of a subgroup of that group to each ideal of $\mathcal{O}_{\mathbb{Q}}$, and an assignment $\mathrm{gen}$ of such a point to each height-one prime; these fill the corresponding slots of the carrier data `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, whose central character group is taken to be $\top$, whose measure on $\mathrm{GL}_2$ of the adeles is the adelic Haar measure for the Borel structure, and whose additive measure $\nu$ on the adeles of $\mathbb{Q}$ is the adelic additive Haar measure conditioned on the adelic box (the product of the infinite box with the integral finite adeles). Let $\psi$ be an additive character of the adeles of $\mathbb{Q}$ with values in $\mathbb{C}$ which is trivial on the image of $\mathbb{Q}$, continuous and nontrivial, and let $\Phi$ be a continuous complex-valued function on $\mathrm{GL}_3$ of the adeles satisfying $\Phi(\gamma g) = \Phi(g)$ for all $\gamma \in \mathrm{GL}_3(\mathbb{Q})$, embedded entrywise by `globalPointsGL`. Assume $\Phi$ satisfies the two cuspidality conditions `IsCuspidalAlongP21` and `IsCuspidalAlongP12` for this carrier data, i.e. for every $g$ the iterated $\nu$-integrals of $\Phi(\mathrm{radicalP21}\,[x,y]\cdot g)$ and of $\Phi(\mathrm{radicalP12}\,[x,y]\cdot g)$ over $x$ and $y$ vanish. Here the Whittaker coefficient is $\mathrm{whittaker3}(\Phi)(g) = \int\!\!\int\!\!\int \Phi(u(x,y,z) g)\,\psi(-(x+y))\,d\nu(z)\,d\nu(y)\,d\nu(x)$ with $u(x,y,z)$ the upper triangular unipotent matrix with entries $x, y, z$, and the index set is the space of right cosets of the image of the upper unipotent homomorphism `unipotentGL2Hom` over $\mathbb{Q}$, each index $i$ giving a translate $\mathrm{mirabolicTranslate}\, i$ obtained by embedding a chosen representative in $\mathrm{GL}_2(\mathbb{Q})$ into $\mathrm{GL}_3$ of the adeles. Assume finally that for every $g$ the family $i \mapsto \mathrm{whittaker3}(\Phi)(\mathrm{mirabolicTranslate}\, i \cdot g)$ is summable. Then for every $g$ this family has sum $\Phi(g)$.
--
--   This is the Fourier–Whittaker expansion of a cuspidal function on $\mathrm{GL}_3$ along the mirabolic subgroup, here in the conditional form: summability of the mirabolic series is assumed, and the assertion is that its sum recovers the function. It is obtained from the corresponding $\mathrm{GL}_2$ expansion [`AutomorphicForm.hasSum_whittakerCoefficient`](thm.html#AutomorphicForm.hasSum_whittakerCoefficient) together with the invariance of the box-conditioned adelic integral under scaling by nonzero rationals, and feeds the construction of cubic induction data used in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.hasSum_whittaker3_mirabolicTranslate_mul_of_summable_of_isCuspidalAlong
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hc : Continuous Φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (mirabolicTranslate i * g))) :
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (mirabolicTranslate i * g))
      (Φ g) := by sorry
