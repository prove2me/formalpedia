-- Prove2me | Theorems.Thm_OAI_SegmentLenses_represented_joint_bound
-- name    : OAI.SegmentLenses.represented_joint_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:18:54.651557+00:00
-- url     : https://prove2.me/theorems/bc330649-cadc-491f-a305-091778267997
-- title:
--   Finite midpoint tail bound for functionals given by a signed finite law of segment representations
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$. For finite $H\subseteq V$ the head and tail of $x\in J_V^{*}$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*}$ and $Q_Hx=x-P_Hx$. A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$.
--
--   A *representation* $A=(\mathcal F,c)$ is a segment family $\mathcal F$ together with real coefficients $(c_S)_{S\in\mathcal F}$. Its value is $\Lambda A=\sum_{S\in\mathcal F}c_S\,\sigma_S\in J_V^{*}$ and its energy is $\mathcal E(A)=\sum_{S\in\mathcal F}c_S^2$. A *finite law* $\mu$ on a finite set $\Omega$ is a weight function with $\mu(\omega)\ge0$ for all $\omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$. For $f$ with values in $\mathbb{R}$ or in $J_V^{*}$ write $\mathbb{E}_\mu f=\sum_{\omega\in\Omega}\mu(\omega)\,f(\omega)$.
--
--   Let $H,K\subseteq V$ be finite with $H$ ancestral. Let $\mu$ be a finite law on a finite set $\Omega$, let $\varepsilon:\Omega\to\mathbb{R}$ satisfy $|\varepsilon(\omega)|\le1$, and for each $\omega\in\Omega$ let $A_\omega=(\mathcal F_\omega,c^\omega)$ be a representation all of whose members are subsets of $K$. Let $x,y\in J_V^{*}$, let $q:V\to\mathbb{R}$ be finitely supported, and let $r,R\in\mathbb{R}$. Assume
--
--   - $P_Hx=x$;
--   - $\mathbb{E}_\mu\big[\Lambda A_\omega\big]=x$ and $\mathbb{E}_\mu\big[\varepsilon(\omega)\,\Lambda A_\omega\big]=y$;
--   - $q(v)=0$ for all $v\notin H$, $\|q\|_{\mathrm{seg}}=r$ and $x(q)=r^2$;
--   - $\mathcal E(A_\omega)\le R^2$ for every $\omega\in\Omega$.
--
--   Then
--   $$
--   \|Q_Hy\|_{J_V^{*}}\le2\sqrt{R^2-r^2}.
--   $$
--
--   This is the finite core of the midpoint-lens inequality. In the main argument, $x+y$ and $x-y$ have norm at most $R$, and each is written, via the atomic-law theorem, as the average of a finite law of representations of energy at most $R^2$ supported in a finite ancestral set $K$. Pooling the two laws with signs $\varepsilon=+1$ and $\varepsilon=-1$ gives a law with average $x$ and signed average $y$. Taking for $q$ the multiple $\|x\|\,q_0$ of a unit norming test $q_0$ of $x$ supported in $H$ gives $r=\|x\|$. The conclusion then reads $\|Q_Hy\|\le2\sqrt{R^2-\|x\|^2}$.
--
--   **Formalization Note** The square root is `Real.sqrt`, which is $0$ for negative arguments; the hypotheses imply $r^2\le R^2$ anyway. The test $q$ is an element of `Test V` with support condition `q.coeff.support ⊆ H`, and $x(q)$ is evaluation at its image in the completion. $\mathbb{E}_\mu$ is `μ.expect`, and the sign function $\varepsilon$ is `σ` in Lean. The section works with classical decidability. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/TailBudget.lean#L81-L170

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

theorem OAI.SegmentLenses.represented_joint_bound {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (A : Ω → Representation V) (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (x y : FullDual V) (hx : head H x = x)
    (hmean : μ.expect (fun ω => (A ω).value) = x)
    (hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y)
    (q : Test V) (hq : q.coeff.support ⊆ H) (r R : ℝ)
    (hqr : ‖q‖ = r) (hxq : x (q : Primal V) = r ^ 2)
    (hR : ∀ ω, (A ω).energy ≤ R ^ 2) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by sorry
