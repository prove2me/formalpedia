-- Prove2me | Theorems.Thm_OAI_Solenoidal_circuit_periodic_bound
-- name    : OAI.Solenoidal.circuit_periodic_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:53:57.630727+00:00
-- url     : https://prove2.me/theorems/831b83fc-56c7-4b9a-b128-b7ded155cd7c
-- title:
--   Explicit uniform bounds on all mixed derivatives of a periodic smooth field given by an arithmetic circuit on the period cell
-- statement:
--   Space-time points are $z=(t,x)=(z_0,z_1,z_2,z_3)$ with $z_0=t$ and $z_{j+1}=x_j$; direction $0$ is time and directions $1,2,3$ are spatial. For a list $\alpha$ of directions, $D^\alpha u$ denotes the iterated partial derivative of a field $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ (for $\alpha=(j,\alpha')$, $D^\alpha u=\partial_{z_j}D^{\alpha'}u$, and $D^{()}u=u$), and $\|w\|_\infty=\max_k|w_k|$ for $w\in\mathbb{R}^3$.
--
--   *Circuits.* Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$, and $\rho(x)=1/\big(\psi(x)+\psi(1-x)\big)$. The one-variable profiles are $P_0(y)=y$, $P_1=\rho$, and $P_{k}(y)=y^{-(k-2)}\psi(y)$ for $k\ge2$ (read as $0$ for $y\le0$). An *atom* is a tuple $(j,a,b,k)$ with $j\in\{0,1,2,3\}$, $a,b\in\mathbb{Q}$, $k\in\mathbb{N}$, evaluating to $z\mapsto P_k(a z_j+b)$. A *circuit* is a finite expression tree whose leaves are rational constants, atoms, or the constant $0$, and whose internal nodes are sums and products; it evaluates to a smooth function $[\![c]\!]$ on space-time. For a triple $e=(e_0,e_1,e_2)$ of circuits let $F_e(z)=\big([\![e_0]\!](z),[\![e_1]\!](z),[\![e_2]\!](z)\big)$.
--
--   *Symbolic derivatives and bounds.* The formal partial derivative $\partial_j c$ of a circuit is defined by the sum rule, the Leibniz rule, $\partial_j(\text{constant})=0$, and the chain rule for atoms: $\partial_j$ of the atom $(i,a,b,k)$ is $0$ if $i\ne j$, and otherwise $a$ times a circuit for $P_k'(a z_j+b)$, using $P_0'=1$, $P_1'(y)=-P_1(y)^2\big(P_4(y)-P_4(1-y)\big)$ and $P_{n+2}'=P_{n+4}-n\,P_{n+3}$. For a list $\alpha$ put $c^{(\,)}=c$ for the empty list and $c^{(j,\alpha')}=\partial_j c^{(\alpha')}$. The syntactic bound $\beta(c,R)\in\mathbb{Q}$ is defined by $\beta=0$ on zero leaves, $\beta(q,R)=|q|$ for a constant $q$, $\beta(c+c',R)=\beta(c,R)+\beta(c',R)$, $\beta(c\cdot c',R)=\beta(c,R)\,\beta(c',R)$, and, for an atom $(j,a,b,k)$, $\beta=|a|\,|R|+|b|$ if $k=0$, $\beta=16$ if $k=1$, $\beta=(k-2)!$ if $k\ge2$. The jet bound of $e$ is $J(e,\alpha)=\sum_{k=0}^{2}\beta\big(e_k^{(\alpha)},10\big)$.
--
--   **Theorem.** Let $u$ be a field that is $C^\infty$ jointly in $(t,x)$, $10$-periodic in each spatial variable ($u(t,x+10k)=u(t,x)$ for $k\in\mathbb{Z}^3$) and $1$-periodic in time ($u(t+1,x)=u(t,x)$). Let $e$ be a triple of circuits with $u=F_e$ on the closed cell $[0,1]\times[0,10]^3$. Then for every list of directions $\alpha$ and every $z\in\mathbb{R}\times\mathbb{R}^3$,
--
--   $$
--   \big\|D^\alpha u(z)\big\|_\infty\le J(e,\alpha).
--   $$
--
--   The bound $J(e,\alpha)$ is a rational number obtained from $e$ and $\alpha$ by purely syntactic manipulations (formal differentiation and evaluation of $\beta$), so it gives explicit uniform bounds for all space-time derivatives of the field, computable from the multi-index by one fixed procedure. This is the form of derivative bounds required by the effective regularity statements for the constructed forcing and velocity fields.
--
--   **Formalization Note** Circuits are elements of Mathlib's `Nat.Partrec.Code`, reinterpreted: `pair` is a sum, `comp` a product, `prec a _` an atom whose parameters are decoded from the code `a`, `rfind' a` a rational constant decoded from `a`, and `zero`, `succ`, `left`, `right` the constant $0$. The bound is `Circuit.jetBound e α`, the norm is Lean's sup norm on `Fin 3 → ℝ`, and the hypotheses are `Smooth u`, `SpatiallyPeriodic u`, `OnePeriodic u` and agreement on `closedPeriodCell`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean#L211-L226

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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms

open OAI OAI.Solenoidal
open Set Filter Encodable
open scoped BigOperators Topology

theorem OAI.Solenoidal.circuit_periodic_bound {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (z : SpaceTime) :
    ‖mixedDerivative u a z‖ ≤ (Circuit.jetBound e a : ℝ) := by sorry
