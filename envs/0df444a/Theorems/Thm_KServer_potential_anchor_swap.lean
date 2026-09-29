-- Prove2me | Theorems.Thm_KServer_potential_anchor_swap
-- name    : KServer.potential_anchor_swap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T22:01:40.163369+00:00
-- url     : https://prove2.me/theorems/33a5f2fa-0374-460a-b1e4-d74437478949
-- title:
--   Exchanging the first two anchors of the Coester-Koutsoupias potential
-- statement:
--   The Coester--Koutsoupias potential of a $3$-server work function $w$, anchored at a triple $x_1, x_2, x_3$, is
--
--   $$\Phi_{x_1x_2x_3}(w) \;=\; w(x_1x_2x_3) + w(\bar x_1 x_2 x_3) + w(\bar x_2 \bar x_2 x_3) + w(\bar x_3\bar x_3\bar x_3),$$
--
--   where $\bar x$ is the antipode of $x$ in the antipodally extended space. The theorem gives a condition under which the first two anchors may be exchanged without increasing the potential:
--
--   $$w(\bar x_2\bar x_2 x_3) = w(\bar x_2 x_1 x_3) + d(x_1, \bar x_2) \;\Longrightarrow\; \Phi_{x_2x_1x_3}(w) \;\le\; \Phi_{x_1x_2x_3}(w).$$
--
--   The hypothesis is the statement that the configuration $\bar x_2\bar x_2 x_3$ **resolves to $x_1$**: one of its two copies of $\bar x_2$ can be sent to $x_1$ at exactly the cost of the move, so that the work function value splits as a value at the moved configuration plus the distance travelled.
--
--   ## Role
--
--   This is the concluding step of Lemma 25 of Coester and Koutsoupias, the anchor-swapping lemma that underlies their proof that the Work Function Algorithm is $3$-competitive for three servers on trees. Their tree argument proceeds by case analysis on which server of the anchor triple resolves the request, and it repeatedly needs to normalise which of $x_1$ and $x_2$ plays the distinguished role; the exchange is legitimate precisely when the resolution hypothesis above holds, which the greedy choice of anchors supplies.
--
--   Only one property of the antipode map is used, and it is not involutivity: it is the symmetry
--
--   $$d(\bar p, q) = d(p, \bar q),$$
--
--   which the antipodal extension satisfies because both sides equal $2\Delta - d(p,q)$. The theorem is therefore stated for an arbitrary map $\mathrm{bar} : M \to M$ with that property, and applies to any metric space carrying one --- in particular to an antipodal extension, but the argument never inspects how the extension was built.
--
--   ## Formalization note
--
--   $w$ is `workFnU`, the work function of an unlabelled configuration; configurations are written as the literals $![\,\cdot,\cdot,\cdot\,]$ of type $\mathrm{Fin}\,3 \to M$. The two facts used about $w$ are its $1$-Lipschitzness with respect to the movement cost and its invariance under permuting the servers, the latter only to identify $w(x_2x_1x_3)$ with $w(x_1x_2x_3)$; the fourth summand is common to both sides and inert.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section on trees, Lemma 25 (lem:treeSwapx12), final display.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem potential_anchor_swap (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (bar : M → M) (hbar : ∀ p q : M, dist (bar p) q = dist p (bar q)) (x₁ x₂ x₃ : M)
    (hres : workFnU C₀ σ ![bar x₂, bar x₂, x₃]
      = workFnU C₀ σ ![bar x₂, x₁, x₃] + dist x₁ (bar x₂)) :
    workFnU C₀ σ ![x₂, x₁, x₃] + workFnU C₀ σ ![bar x₂, x₁, x₃]
        + workFnU C₀ σ ![bar x₁, bar x₁, x₃] + workFnU C₀ σ ![bar x₃, bar x₃, bar x₃]
      ≤ workFnU C₀ σ ![x₁, x₂, x₃] + workFnU C₀ σ ![bar x₁, x₂, x₃]
        + workFnU C₀ σ ![bar x₂, bar x₂, x₃] + workFnU C₀ σ ![bar x₃, bar x₃, bar x₃] := by sorry

end KServer
