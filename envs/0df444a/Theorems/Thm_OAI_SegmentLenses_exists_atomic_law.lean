-- Prove2me | Theorems.Thm_OAI_SegmentLenses_exists_atomic_law
-- name    : OAI.SegmentLenses.exists_atomic_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:18:05.772359+00:00
-- url     : https://prove2.me/theorems/78e7ae09-2b76-4dc7-ace9-96886a978d80
-- title:
--   Dual functionals supported on a finite ancestral set are means of finite laws of segment representations of energy at most $R^2$
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$. For finite $H\subseteq V$ the head and tail of $x\in J_V^{*}$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*}$ and $Q_Hx=x-P_Hx$. A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$.
--
--   A *representation* $A=(\mathcal F,c)$ is a segment family $\mathcal F$ together with real coefficients $(c_S)_{S\in\mathcal F}$. Its value is $\Lambda A=\sum_{S\in\mathcal F}c_S\,\sigma_S\in J_V^{*}$ and its energy is $\mathcal E(A)=\sum_{S\in\mathcal F}c_S^2$. A *finite law* $\mu$ on a finite set $\Omega$ is a weight function with $\mu(\omega)\ge0$ for all $\omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$.
--
--   Let $K\subseteq V$ be finite and ancestral. Let $\mathcal L_K$ be the finite set of local families of $K$, i.e. of segment families all of whose members are subsets of $K$, and let $\Omega_K=\{\ast\}\cup\mathcal L_K$ be obtained by adjoining one extra point $\ast$. Let $z\in J_V^{*}$ satisfy $P_Kz=z$, and let $R>0$ with $\|z\|\le R$. Then there exist a finite law $\mu$ on $\Omega_K$ and representations $A_\omega=(\mathcal F_\omega,c^\omega)$, $\omega\in\Omega_K$, such that
--
--   1. $\mathcal E(A_\omega)\le R^2$ for every $\omega\in\Omega_K$;
--   2. every member of every family $\mathcal F_\omega$ is a subset of $K$;
--   3. the $\mu$-average of the values is $z$:
--   $$
--   \sum_{\omega\in\Omega_K}\mu(\omega)\,\Lambda A_\omega=z .
--   $$
--
--   Thus every such functional is the barycenter of a finite probability distribution on segment representations of energy at most $R^2$ supported in $K$. In the midpoint-lens argument it is applied to $x+y$ and $x-y$, and the two resulting laws are pooled with signs $+1$ and $-1$, which produces the input of the finite tail bound.
--
--   **Formalization Note** $\Omega_K$ is `Option (LocalFamily K)`, with `none` playing the role of $\ast$. The average is `μ.expect (fun ω => (A ω).value)`, the weighted sum in `FullDual V`. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/GateRecovery.lean#L286-L314

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
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem OAI.SegmentLenses.exists_atomic_law {K : Finset V} (hK : Ancestral (· ≤ ·) K)
    (z : FullDual V) (hz : head K z = z) {R : ℝ} (hR : 0 < R) (hn : ‖z‖ ≤ R) :
    ∃ μ : FiniteLaw (Option (LocalFamily K)),
      ∃ A : Option (LocalFamily K) → Representation V,
        (∀ ω, (A ω).energy ≤ R ^ 2) ∧
        (∀ ω S, S ∈ (A ω).family.sets → S ⊆ K) ∧
        μ.expect (fun ω => (A ω).value) = z := by sorry
