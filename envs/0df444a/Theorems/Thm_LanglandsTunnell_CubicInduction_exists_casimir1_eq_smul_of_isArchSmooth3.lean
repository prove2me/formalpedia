-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3
-- name    : LanglandsTunnell.CubicInduction.exists_casimir1_eq_smul_of_isArchSmooth3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/21394cfb-420e-5c29-bcd3-6b00c79bdb8a
-- title:
--   Linear central element acts by a scalar
-- statement:
--   Fix a group homomorphism $\omega \colon (\mathbb{A}_{\mathbb{Q}})^{\times} \to \mathbb{C}^{\times}$ from the units of the adele ring of $\mathbb{Q}$ (formed over $\mathcal{O}_{\mathbb{Q}}$) to $\mathbb{C}^{\times}$, and a function $u \colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ on the group of invertible $3 \times 3$ matrices over the adele ring. Assume two hypotheses. First, $u$ transforms under the centre by $\omega$: for every idele unit $z$ and every $g$, one has $u(\mathrm{diag}(z,z,z)\,g) = \omega(z)\,u(g)$, where $z$ is sent into $\mathrm{GL}_3$ by the scalar-matrix homomorphism `centralScalarGL`. Second, [`WhittakerBlock.IsArchSmooth3 u`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) holds: for every $g$, the map $e \mapsto u\bigl(g \cdot \mathtt{archRealLift3}\,e\bigr)$, defined on the nine real entries $e \colon \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$, is $C^{\infty}$ on the open set where $\det(e) \neq 0$; here $\mathtt{archRealLift3}\,e$ is the unit of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ attached to the adelic matrix $\mathtt{archRealMat3}\,e$ when the latter is invertible, and $1$ otherwise. The conclusion is that there exists a single constant $c \in \mathbb{C}$ with $\mathtt{WhittakerBlock.casimir1}\,u = c \cdot u$ as functions, where $(\mathtt{casimir1}\,u)(g) = \sum_{i=1}^{3} \frac{d}{ds}\bigl|_{s=0} u\bigl(g \cdot \mathtt{archRealLift3}(1 + s\,E_{ii})\bigr)$ is the sum of the three diagonal right derivatives at the archimedean place.
--
--   This is the degree-one instance of the classical fact that the centre of the universal enveloping algebra acts by scalars on a function possessing a central character: here only the element $E_{11}+E_{22}+E_{33}$ of $\mathfrak{gl}_3(\mathbb{R})$, the infinitesimal generator of the scalar subgroup $\mathbb{R}^{\times} \cdot 1 \subset \mathrm{GL}_3(\mathbb{R})$, is involved. It feeds the archimedean estimates for Whittaker functions along the diagonal torus used in the cubic-induction construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_casimir1_eq_smul_of_isArchSmooth3
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u) :
    ∃ c : ℂ, WhittakerBlock.casimir1 u = c • u := by sorry
