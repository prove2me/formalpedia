-- Prove2me | Theorems.Thm_OAI_Solenoidal_mixedDerivative_eqOn_cell
-- name    : OAI.Solenoidal.mixedDerivative_eqOn_cell
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:45:06.472921+00:00
-- url     : https://prove2.me/theorems/8525547e-8be2-4b61-94c2-b79007e29e77
-- title:
--   Smooth fields agreeing on the closed space-time cell $[0,1]\times[0,10]^3$ have equal mixed derivatives there
-- statement:
--   Write space-time points as $z=(t,x)\in\mathbb{R}\times\mathbb{R}^3$ and label the coordinate directions by $0,1,2,3$: direction $0$ is time, $\varepsilon_0=(1,0)$, and direction $j+1$ is the spatial direction $\varepsilon_{j+1}=(0,e_j)$ for $j=0,1,2$. A field is a map $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$; it is *smooth* if it is $C^\infty$ jointly in $(t,x)$. For a finite list $\alpha=(j_1,\dots,j_k)$ of directions the mixed derivative $D^\alpha u$ is defined recursively by
--   $$D^{()}u=u,\qquad D^{(j,\alpha')}u(z)=D\big(D^{\alpha'}u\big)(z)\,[\varepsilon_j],$$
--   so that $D^\alpha u=\partial_{j_1}\partial_{j_2}\cdots\partial_{j_k}u$. Let $K=[0,1]\times[0,10]^3$ be the closed period cell.
--
--   **Theorem.** Let $u$ and $v$ be smooth fields with $u=v$ on $K$. Then for every list of directions $\alpha$,
--
--   $$
--   D^\alpha u(z)=D^\alpha v(z)\qquad\text{for all } z\in K .
--   $$
--
--   The cell $K$ is closed, so the statement includes boundary points, where derivatives are not determined by the values on $K$ alone without some argument. The theorem allows a smooth periodic field to be replaced, together with all its derivatives, by an explicit formula that is only known to agree with it on the closed period cell; periodicity then transports the information to all of space-time.
--
--   **Formalization Note** `mixedDerivative u α` is defined with Mathlib's Fréchet derivative `fderiv`, the list is consumed from the front, and $K$ is `closedPeriodCell`, the order interval `Set.Icc (0,0) (1, fun _ => 10)` in $\mathbb{R}\times\mathbb{R}^3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/BoxJets.lean#L155-L172

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets

open OAI OAI.Solenoidal
open Set MeasureTheory Filter
open scoped BigOperators Topology

theorem OAI.Solenoidal.mixedDerivative_eqOn_cell {u v : Field} (hu : Smooth u) (hv : Smooth v)
    (h : Set.EqOn (fun z => u z.1 z.2) (fun z => v z.1 z.2) closedPeriodCell)
    (α : List (Fin 4)) :
    Set.EqOn (mixedDerivative u α) (mixedDerivative v α) closedPeriodCell := by sorry
