-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_coordinate_index_integral
-- name    : OAI.ThreeManifold.Neck.coordinate_index_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:15:35.164097+00:00
-- url     : https://prove2.me/theorems/99399ba7-c40e-4ef6-ac14-6534609a431f
-- title:
--   Integrated index-form identity in coordinates $dt^2+Q(t)$
-- statement:
--   For a real $2\times 2$ matrix $A$ and $u,v\in\mathbb{R}^2$ write $\langle u,v\rangle_A = u^{\mathsf T}Av$. Elements of $\mathbb{R}\times\mathbb{R}^2$ are written $U=(U^0,\bar U)$ with $U^0\in\mathbb{R}$ and $\bar U\in\mathbb{R}^2$. For $2\times2$ matrices $P,Q,A,B$ let $g_Q$, $\Gamma_{P,A}$, $\mathcal{R}_{P,A,B}$, $e_{Q,A,B}$, $b_{P,A,B}$ and $\beta_A$ be as follows:
--
--   - $g_Q(U,V)=U^0V^0+\langle\bar U,\bar V\rangle_Q$;
--   - the connection term $\Gamma_{P,A}(U,V) = \bigl(-\tfrac12\langle\bar U,\bar V\rangle_A,\ \tfrac12\,(U^0\,PA\bar V + V^0\,PA\bar U)\bigr)$;
--   - $\Gamma'_{P,A,B}(U,V)=\bigl(-\tfrac12\langle\bar U,\bar V\rangle_B,\ \tfrac12(U^0S\bar V+V^0S\bar U)\bigr)$ with $S=PB-PAPA$;
--   - $\mathcal{R}_{P,A,B}(U,V,W)=U^0\Gamma'(V,W)-V^0\Gamma'(U,W)+\Gamma(U,\Gamma(V,W))-\Gamma(V,\Gamma(U,W))$;
--   - $e_{Q,A,B}(T,V,\dot V)=(\dot V^0)^2+\langle\dot{\bar V},\dot{\bar V}\rangle_Q+2V^0\langle\dot{\bar V},\bar T\rangle_A+\tfrac12(V^0)^2\langle\bar T,\bar T\rangle_B$;
--   - $\beta_A(T,V)=-\tfrac12T^0\langle\bar V,\bar V\rangle_A+V^0\langle\bar T,\bar V\rangle_A$;
--   - $b_{P,A,B}$ is the boundary jet
--
--   $$
--   \begin{aligned}
--   b_{P,A,B}(T,V,\dot V) ={}& -\tfrac14\langle\bar T,\bar T\rangle_A\langle\bar V,\bar V\rangle_A - T^0\langle\dot{\bar V},\bar V\rangle_A - \tfrac12 (T^0)^2\langle\bar V,\bar V\rangle_B \\
--   &+ \dot V^0\langle\bar V,\bar T\rangle_A + V^0\langle\dot{\bar V},\bar T\rangle_A + V^0T^0\langle\bar V,\bar T\rangle_B - V^0T^0\langle\bar V,\bar T\rangle_{APA}.
--   \end{aligned}
--   $$
--
--   **Theorem.** Let $P,Q,A,B:\mathbb{R}\to\mathbb{R}^{2\times2}$, $t,v,w,w_d:\mathbb{R}\to\mathbb{R}$, $u,z,z_d:\mathbb{R}\to\mathbb{R}^2$, and $a,c\in\mathbb{R}$. Let $I=[\min(a,c),\max(a,c)]$, and for $s\in I$ abbreviate $P_s=P(t(s))$, and similarly $Q_s$, $A_s$, $B_s$, and $T_s=(v(s),u(s))$, $V_s=(w(s),z(s))$, $\dot V_s=(w_d(s),z_d(s))$. Assume:
--
--   1. $P\circ t$, $Q\circ t$, $A\circ t$, $B\circ t$, $v$, $u$, $w$, $z$, $w_d$, $z_d$ are continuous on $I$;
--   2. for every $s\in I$: $Q_sP_s=I$, and $Q_s$, $P_s$, $A_s$, $B_s$ are symmetric;
--   3. for every $s\in I$: $t'(s)=v(s)$, $v'(s)=\tfrac12\langle u(s),u(s)\rangle_{A_s}$, $u'(s)=-v(s)\,P_sA_s\,u(s)$, $A$ is differentiable at $t(s)$ with $A'(t(s))=B_s$, $w'(s)=w_d(s)$ and $z'(s)=z_d(s)$, all as two-sided derivatives at $s$.
--
--   Then
--   $$
--   \int_a^c\Bigl[g_{Q_s}\bigl(\dot V_s+\Gamma_{P_s,A_s}(T_s,V_s),\,\dot V_s+\Gamma_{P_s,A_s}(T_s,V_s)\bigr)-g_{Q_s}\bigl(V_s,\mathcal{R}_{P_s,A_s,B_s}(V_s,T_s,T_s)\bigr)\Bigr]ds
--   =\int_a^c e_{Q_s,A_s,B_s}(T_s,V_s,\dot V_s)\,ds-\Bigl(\beta_{A_c}(T_c,V_c)-\beta_{A_a}(T_a,V_a)\Bigr).
--   $$
--
--   For the metric $dt^2+Q(t)_{ij}dx^idx^j$ with $P=Q^{-1}$, $A=\partial_tQ$ and $B=\partial_t^2Q$, hypothesis 3 says that $s\mapsto(t(s),\cdot)$ is a geodesic with velocity $T_s$, and that $\dot V_s$ is the coordinate derivative of the field $V_s$. The left side is then the index form of $V$ along the geodesic. The theorem expresses it as an explicit energy integral plus endpoint terms, which is the form used to show positivity of the index form in the neck.
--
--   **Formalization Note** $\int_a^c$ is the oriented interval integral, so it changes sign when $a>c$. The interval $I$ is Lean's `Set.uIcc a c`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L365-L421

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Neck.coordinate_index_integral
    {P Q A B : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {wd : ℝ → ℝ} {zd : ℝ → TVec} {a c : ℝ}
    (hP : ContinuousOn (P ∘ t) (Set.uIcc a c))
    (hQ : ContinuousOn (Q ∘ t) (Set.uIcc a c))
    (hA : ContinuousOn (A ∘ t) (Set.uIcc a c))
    (hB : ContinuousOn (B ∘ t) (Set.uIcc a c))
    (hv : ContinuousOn v (Set.uIcc a c)) (hu : ContinuousOn u (Set.uIcc a c))
    (hw : ContinuousOn w (Set.uIcc a c)) (hz : ContinuousOn z (Set.uIcc a c))
    (hwd : ContinuousOn wd (Set.uIcc a c)) (hzd : ContinuousOn zd (Set.uIcc a c))
    (hQP : ∀ s ∈ Set.uIcc a c, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ Set.uIcc a c, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ Set.uIcc a c, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ Set.uIcc a c, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ Set.uIcc a c, (B (t s))ᵀ = B (t s))
    (ht : ∀ s ∈ Set.uIcc a c, HasDerivAt t (v s) s)
    (hv' : ∀ s ∈ Set.uIcc a c,
      HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu' : ∀ s ∈ Set.uIcc a c,
      HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hA' : ∀ s ∈ Set.uIcc a c, HasDerivAt A (B (t s)) (t s))
    (hw' : ∀ s ∈ Set.uIcc a c, HasDerivAt w (wd s) s)
    (hz' : ∀ s ∈ Set.uIcc a c, HasDerivAt z (zd s) s) :
    (∫ s in a..c,
      metric (Q (t s)) ((wd s, zd s) + gamma (P (t s)) (A (t s)) (v s, u s) (w s, z s))
        ((wd s, zd s) + gamma (P (t s)) (A (t s)) (v s, u s) (w s, z s)) -
      metric (Q (t s)) (w s, z s)
        (curvatureJet (P (t s)) (A (t s)) (B (t s)) (w s, z s) (v s, u s) (v s, u s))) =
    (∫ s in a..c,
      coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) := by sorry
