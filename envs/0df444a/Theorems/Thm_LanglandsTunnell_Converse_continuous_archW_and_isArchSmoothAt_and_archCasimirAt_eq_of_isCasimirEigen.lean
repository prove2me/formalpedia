-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
-- name    : LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/683b8cca-ffb0-5722-b452-3b2959232ed4
-- title:
--   Assembled archimedean Whittaker function is a Casimir eigenfunction
-- statement:
--   Let $K$ be a number field. Let $archR$ assign to each real infinite place $w$ of $K$ a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$, $a_i\in\mathbb Z/2$, or $\mathrm{discrete}(u,k)$ with $k\ge 1$), let $archC$ assign to each complex place a complex archimedean parameter $(u_1,k_1,u_2,k_2)$, and let $dR$, $dC$ assign to each real, respectively complex, place an archimedean Whittaker datum `ArchDatumR`, `ArchDatumC` for the corresponding parameter (a function $W$ on $2\times2$ matrices over $\mathbb R$, respectively $\mathbb C$, smooth on the invertible locus, with the prescribed unipotent and central transformation laws, an entire zeta function with functional equation, finite order and the stated decay bounds). Fix a real place $w$, and assume the datum $dR\,w$ satisfies the Casimir eigen-equation on invertible real matrices: $\mathrm{matrixCasimir}\,((dR\,w).W)(x)=\lambda\,(dR\,w).W(x)$ for all $x$ with $\det x\ne 0$, where $\mathrm{matrixCasimir}$ is $-\bigl((1/4)H^2-(1/2)H+EF^-\bigr)$ in the matrix flow derivatives and $\lambda=\mathrm{laplaceEigenvalue}(archR\,w)$ equals $1/4-((u_1-u_2)/2)^2$ in the principal case and $(1-k^2)/4$ in the discrete case. Then the assembled function $\Phi=\mathrm{archW}$, defined on $\mathrm{GL}_2(\mathbb A_K)$ as the product over all infinite places $v$ of $(dR\,v).W$ of the real component of $g$ at $v$ when $v$ is real and of $(dC\,v).W$ of the complex component otherwise, satisfies four assertions simultaneously: $\Phi$ is continuous; $\Phi(gk)=\Phi(g)$ for all $g,k$ with $\mathrm{glArch}(k)=1$, i.e. $\Phi$ is invariant under right translation by adelic matrices whose archimedean image is trivial; $\Phi$ is archimedean-smooth at $w$, meaning that for every $g$ the map $e\mapsto\Phi(g\cdot\mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on $\{e\mid \det(\mathrm{of}\,e)\ne 0\}$; and $\mathrm{archCasimirAt}\,hw\,\Phi=\lambda\cdot\Phi$ as functions on all of $\mathrm{GL}_2(\mathbb A_K)$, where $\mathrm{archCasimirAt}$ is the same Casimir combination formed from the adelic flow derivatives at $w$.
--
--   This is the compatibility statement linking the place-by-place notion of a real archimedean Whittaker datum satisfying the Casimir eigen-equation on $\mathrm{GL}_2(\mathbb R)$ with the adelic archimedean differential operators at a single real place: the three one-parameter flows at $w$ move only the $w$-component, so the assembled Euler product over infinite places inherits the eigenvalue of its $w$-factor. It is used in the converse-theorem direction of Langlands–Tunnell, where the archimedean Whittaker function of a candidate automorphic form is built from local data and must be shown to be continuous, to depend only on the archimedean component, and to be a Casimir eigenfunction with the prescribed Laplace eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
    (K : Type) [Field K] [NumberField K]
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (hw : w.IsReal)
    (h : ArchCasimir.IsCasimirEigen (dR w hw)) :
    Continuous (archW archR archC dR dC) ∧
    (∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → archW archR archC dR dC (g * k) = archW archR archC dR dC g) ∧
    IsArchSmoothAt hw (archW archR archC dR dC) ∧
    archCasimirAt hw (archW archR archC dR dC) = (laplaceEigenvalue (archR w hw)) • archW archR archC dR dC := by sorry
