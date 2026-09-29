-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator
-- name    : LanglandsTunnell.CubicInduction.SlabL2.casimir_smoothingOperator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/8a074a6e-c9ef-5636-b460-d49e5fd66d73
-- title:
--   Casimir operators commute with smoothing on GL₃(A_ℚ)
-- statement:
--   Let $\varphi, H \colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be complex-valued functions on the adelic group `AdelicGL 3 (𝓞 ℚ) ℚ`. Assume first that $\varphi$ is a smoothing kernel in the sense of `IsSmoothingKernel`: there are a function $\alpha$ on real $3 \times 3$ arrays which is $C^\infty$, has compact support and has topological support contained in $\{m : \det m \neq 0\}$, and subgroups $K'_p \le \mathrm{GL}_3(\mathbb{Q}_p)$, one for each height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, each open and compact and equal to the maximal compact subgroup `localMaximalCompact3` for all but finitely many $p$, such that $\varphi(g) = \alpha(\mathrm{archEntries}\,g)$ times the indicator of the set of $g$ all of whose finite components lie in the corresponding $K'_p$, where $\mathrm{archEntries}$ records the real coordinates of the entries of $g$. Assume next `IsArchSmooth3 H`: for every $g$ the map $e \mapsto H(g \cdot \mathrm{archRealLift3}\,e)$ from real $3\times 3$ arrays to $\mathbb{C}$ is $C^\infty$ on $\{e : \det e \neq 0\}$, $\mathrm{archRealLift3}$ sending an invertible array to the corresponding archimedean element and a singular one to $1$. Assume finally that for every list $l$ of pairs $(i,j) \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$ the iterated derivative of $H$ obtained by applying the operators $\mathrm{archDeriv}\,i\,j$ along $l$ (right to left) is continuous, where $(\mathrm{archDeriv}\,i\,j\,F)(g)$ is the derivative at $s = 0$ of $s \mapsto F\bigl(g \cdot \mathrm{archRealLift3}(1 + sE_{ij})\bigr)$. Writing $(R_\varphi f)(x) = \int \varphi(g) f(xg)\,dg$ for the smoothing operator against the adelic Haar measure `adelicGLHaar` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, the conclusion is the conjunction of three identities: $C_k(R_\varphi H) = R_\varphi(C_k H)$ for $k = 1,2,3$, where $C_1 = \sum_i \mathrm{archDeriv}\,i\,i$, $C_2 = \sum_{i,j} \mathrm{archDeriv}\,i\,j \circ \mathrm{archDeriv}\,j\,i$ and $C_3 = \sum_{i,j,k} \mathrm{archDeriv}\,i\,j \circ \mathrm{archDeriv}\,j\,k \circ \mathrm{archDeriv}\,k\,i$.
--
--   This is the concrete form, for the linear, quadratic and cubic central elements built from the elementary right derivatives at the archimedean place of $\mathrm{GL}_3$, of the standard fact that right convolution operators commute with the centre of the universal enveloping algebra. It is used in the spectral analysis of the cuspidal slab, where smoothing operators are shown to preserve spaces of Casimir eigenfunctions and to produce smooth eigenvectors inside irreducible cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.CubicInduction.SlabL2.casimir_smoothingOperator
    (φ H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (hH : WhittakerBlock.IsArchSmooth3 H)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) H)) :
    WhittakerBlock.casimir1 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir1 H) ∧
      WhittakerBlock.casimir2 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir2 H) ∧
        WhittakerBlock.casimir3 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir3 H) := by sorry
