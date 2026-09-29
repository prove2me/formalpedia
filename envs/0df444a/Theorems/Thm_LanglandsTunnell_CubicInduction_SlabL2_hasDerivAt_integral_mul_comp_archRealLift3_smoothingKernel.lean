-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
-- name    : LanglandsTunnell.CubicInduction.SlabL2.hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/bc82f245-d00e-56f8-bd3d-3934ed417aef
-- title:
--   Archimedean derivatives of smoothed coefficients on GL₃(A_ℚ)
-- statement:
--   Let $c\colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be continuous, let $\varphi\colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ satisfy `IsSmoothingKernel`, i.e. there are a smooth compactly supported $\alpha$ on $3\times 3$ real matrices whose topological support consists of matrices of nonzero determinant, and subgroups $K'_p\le \mathrm{GL}_3(\mathbb{Q}_p)$ that are open and compact and equal `localMaximalCompact3` for all but finitely many $p$, such that $\varphi(g)=\alpha(\mathrm{archEntries}\,g)$ times the indicator of $\{x:\ \forall p,\ x_p\in K'_p\}$; and let $k\in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$. All integrals are against the Haar measure `adelicGLHaar` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ for its Borel structure, and $L(e)=$ `archRealLift3` $e$ is the adelic matrix with archimedean entries $e$ (interpreted as $1$ if not invertible). Write $(X_{ij}\varphi)(y)=-\frac{d}{ds}\big|_{0}\varphi(L(I+sE_{ij})y)$. Two assertions hold. First, for all $i,j$, the map $s\mapsto\int\varphi(h)\,c(k\,L(I+sE_{ij})\,h)\,dh$ has derivative $\int (X_{ij}\varphi)(h)\,c(kh)\,dh$ at $s=0$. Second, for $c_1<c_2$, the map sending $s$ to the same integral with $L(I+sE_{ij})$ replaced by the lift of the plane rotation with $\cos s$ in positions $(c_1,c_1),(c_2,c_2)$, $-\sin s$ at $(c_1,c_2)$, $\sin s$ at $(c_2,c_1)$ and $1$ elsewhere on the diagonal, has derivative $\int (X_{c_2c_1}\varphi)(h)c(kh)\,dh-\int (X_{c_1c_2}\varphi)(h)c(kh)\,dh$ at $s=0$.
--
--   This records the infinitesimal action at the archimedean place of the elementary one-parameter subgroups and of the plane rotations on a coefficient $k\mapsto\int\varphi(h)c(kh)\,dh$ smoothed by a kernel $\varphi$, the derivative being expressed by the derived kernel $X_{ij}\varphi$. It feeds the statements about the smoothing module in the cubic induction, namely those on regularity and growth, on stability of the module under archimedean derivatives together with finiteness of orthogonality conditions, and on the leading coefficient of the expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.SlabL2.hasDerivAt_integral_mul_comp_archRealLift3_smoothingKernel
    (c : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous c) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ i j : Fin 3,
      HasDerivAt
        (fun s : ℝ => ∫ h, φ h * c (k * WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
        (∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0) h * c (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) 0) ∧
    (∀ c₁ c₂ : Fin 3, c₁ < c₂ →
      HasDerivAt
        (fun s : ℝ => ∫ h, φ h * c (k * WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0) * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
        ((∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c₂ ∧ b = c₁ then s else 0) * y)) 0) h * c (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) -
         (∫ h, (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c₁ ∧ b = c₂ then s else 0) * y)) 0) h * c (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))) 0) := by sorry
