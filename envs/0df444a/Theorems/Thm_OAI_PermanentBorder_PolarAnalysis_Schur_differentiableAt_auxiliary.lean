-- Prove2me | Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_Schur_differentiableAt_auxiliary
-- name    : OAI.PermanentBorder.PolarAnalysis.Schur.differentiableAt_auxiliary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:41:12.396554+00:00
-- url     : https://prove2.me/theorems/833c67f6-9280-49a8-95bf-6e4a8e0b25c8
-- title:
--   Differentiability of the kernel-vector equations of a bordered matrix family
-- statement:
--   Let $V$ be a complex normed space and $\iota$ a finite index set, and let $\beta,\gamma:V\to\mathbb{C}^{\iota}$ and $E:V\to\mathbb{C}^{\iota\times\iota}$ be maps whose coordinate functions $y\mapsto\beta(y)_i$, $y\mapsto\gamma(y)_i$ and $y\mapsto E(y)_{ij}$ are all complex differentiable at a point $x\in V$. Define the auxiliary map
--   $$\mathcal A:V\times\big(\mathbb{C}^{\iota}\times\mathbb{C}^{\iota}\big)\to\mathbb{C}^{\iota}\times\mathbb{C}^{\iota},\qquad\mathcal A\big(y,(u,w)\big)=\big(\gamma(y)+E(y)\,u,\ \beta(y)^{\top}+w^{\top}E(y)\big).$$
--   Then for every $(u_0,w_0)\in\mathbb{C}^{\iota}\times\mathbb{C}^{\iota}$
--
--   $$
--   \mathcal A\ \text{ is complex differentiable at }\ \big(x,(u_0,w_0)\big).
--   $$
--
--   For a bordered matrix $M(y)=\begin{pmatrix}a(y)&\beta(y)^{\top}\\ \gamma(y)&E(y)\end{pmatrix}$, the equation $\mathcal A(y,(u,w))=0$ says that $M(y)\,(1,u)^{\top}$ vanishes in all rows indexed by $\iota$ and that $(1,w^{\top})\,M(y)$ vanishes in all columns indexed by $\iota$. So $\mathcal A$ encodes normalised right and left kernel vectors as auxiliary unknowns, and its differentiability is needed to apply elimination arguments to the enlarged system.
--
--   **Formalization Note** The map is `auxiliary β γ E`, with $E(y)u$ written `E y *ᵥ u` and $w^{\top}E(y)$ written `w ᵥ* E y`. Only finiteness of $\iota$ is needed (no decidable equality).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SchurDifferentials.lean#L174-L197

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials

open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis OAI.PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [DecidableEq ι] in
theorem OAI.PermanentBorder.PolarAnalysis.Schur.differentiableAt_auxiliary {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ}
    {x : V} {w : (ι → ℂ) × (ι → ℂ)}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (auxiliary β γ E) (x,w) := by sorry
