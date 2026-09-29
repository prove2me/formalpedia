-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isCuspidalAlongP21_mirabolicSeries
-- name    : LanglandsTunnell.CubicInduction.isCuspidalAlongP21_mirabolicSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/18f2da3f-7637-566c-b613-4983767386a3
-- title:
--   Cuspidality along P_{2,1} of the mirabolic Whittaker series
-- statement:
--   Let $\psi$ be an additive character of the adele ring $\mathbb{A}$ of $\mathbb{Q}$ with values in $\mathbb{C}$, assumed to be a global additive character (trivial on the image of $\mathbb{Q}$, continuous, and nontrivial), and let $W : \mathrm{GL}_3(\mathbb{A}) \to \mathbb{C}$ be a $\psi$-Whittaker function in the sense that $W(u(x,y,z)\,g) = \psi(x+y)\,W(g)$ for all $x,y,z \in \mathbb{A}$ and all $g$, where $u(x,y,z)$ is the upper unitriangular matrix with entries $x$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$. Let $D \subseteq \mathrm{GL}_2(\mathbb{A})$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A})$ indexed by the ideals of $\mathbb{Z}$, and a family $gen$ of elements of $\mathrm{GL}_2(\mathbb{A})$ indexed by the finite places be arbitrary; these, together with the box $B \subseteq \mathbb{A}$ consisting of the adeles whose archimedean part lies in the infinite box and whose finite part is integral, assemble into the carrier data `productionPinsOf`, whose central subgroup is all of $\mathbb{A}^\times$, whose measure on $\mathrm{GL}_2(\mathbb{A})$ is the adelic Haar measure for the Borel structure, and whose measure $\nu$ on $\mathbb{A}$ is the adelic additive Haar measure conditioned on $B$. Set $\Phi(x) = \sum_{i}' W(\gamma_i\,x)$, the unconditional sum over the classes $i$ of $N(\mathbb{Q}) \backslash \mathrm{GL}_2(\mathbb{Q})$, where $N$ is the image of the homomorphism $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$ and $\gamma_i$ denotes the chosen representative of $i$, viewed in $\mathrm{GL}_2(\mathbb{A})$ and embedded in the upper left corner of $\mathrm{GL}_3(\mathbb{A})$ (the sum being $0$ where the family is not summable). Then $\Phi$ is cuspidal along the radical of $P_{2,1}$ for this carrier data: for every $g \in \mathrm{GL}_3(\mathbb{A})$,
--   $$\int \int \Phi\bigl(r(x,y)\,g\bigr)\,d\nu(x)\,d\nu(y) = 0,$$
--   where $r(x,y) = u(0,y,x)$ runs over the unipotent radical of the $(2,1)$ maximal parabolic. No convergence or integrability hypothesis is imposed.
--
--   This is the vanishing of the constant term, along the unipotent radical of the maximal parabolic of type $(2,1)$, of the series attached to a $\mathrm{GL}_3$ Whittaker function by summing over $N(\mathbb{Q}) \backslash \mathrm{GL}_2(\mathbb{Q})$ in the mirabolic corner; it is one of the two halves of the Fourier expansion of that series along the radical. It feeds [`LanglandsTunnell.CubicInduction.mirabolicSeries_eq_dual_of_radicalCoefficient_eq`](thm.html#LanglandsTunnell.CubicInduction.mirabolicSeries_eq_dual_of_radicalCoefficient_eq) and the construction of the automorphy datum in [`LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe`](thm.html#LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isCuspidalAlongP21_mirabolicSeries.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isCuspidalAlongP21_mirabolicSeries
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
    IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ))
      (fun x => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * x)) := by sorry
