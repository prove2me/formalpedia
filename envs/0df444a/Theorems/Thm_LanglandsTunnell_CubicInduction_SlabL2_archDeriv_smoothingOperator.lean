-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
-- name    : LanglandsTunnell.CubicInduction.SlabL2.archDeriv_smoothingOperator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/86babe60-bc9c-5237-b693-5fa4ee8ca597
-- title:
--   Archimedean derivative of a smoothing operator along Eᵢⱼ
-- statement:
--   Fix $\varphi, F : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$, where $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ is `AdelicGL 3 (𝓞 ℚ) ℚ`. Assume `IsSmoothingKernel φ`, i.e. there are a function $\alpha$ on real $3\times 3$ arrays which is $C^\infty$, compactly supported and whose topological support consists of arrays with nonzero determinant, together with subgroups $K'_p \le \mathrm{GL}_3(\mathbb{Q}_p)$, one for each finite place $p$ of $\mathbb{Q}$, each open and compact and equal to `localMaximalCompact3` (matrices whose entries and whose inverse's entries have valuation $\le 1$) for all but finitely many $p$, such that $\varphi(g) = \alpha(\mathrm{archEntries}(g))$ times the indicator of $\{x : \forall p,\ x_p \in K'_p\}$. Assume $F$ is locally integrable for the Haar measure `adelicGLHaar` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, and fix $i, j \in \{0,1,2\}$. Write $e(s)$ for `archRealLift3` applied to the array $1 + sE_{ij}$, that is, the adelic matrix which is the archimedean image of $1 + sE_{ij}$ (taken to be $1$ if that matrix fails to be a unit), and set $\varphi'(y) = -\frac{d}{ds}\big|_{s=0}\,\varphi(e(s)\,y)$. The conclusion is twofold: $\varphi'$ is again a smoothing kernel in the above sense, and `archDeriv i j` applied to $x \mapsto \int \varphi(g) F(xg)\,dg$, namely $\frac{d}{ds}\big|_{s=0} \int \varphi(g) F(x\,e(s)\,g)\,dg$, equals $x \mapsto \int \varphi'(g) F(xg)\,dg$.
--
--   This is the transfer of an infinitesimal right translation along the elementary matrix $E_{ij}$ from the function being smoothed to the smoothing kernel, the mechanism by which smoothing operators on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ produce smooth vectors with a differentiable action of the archimedean Lie algebra. It is used in the iterated form needed to compute the Casimir action on smoothings and to show that spaces of cuspidal $L^2$-functions with prescribed Casimir eigenvalue are stable under smoothing operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory IsDedekindDomain AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.glBorel in

theorem LanglandsTunnell.CubicInduction.SlabL2.archDeriv_smoothingOperator
    (φ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (hF : LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    IsSmoothingKernel (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0) ∧
      WhittakerBlock.archDeriv i j (smoothingOperator φ F) =
        smoothingOperator (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0) F := by sorry
