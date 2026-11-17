-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_16
-- name    : MonoidProdQ.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:14:59.658528+00:00
-- url     : https://prove2.me/theorems/4425ee2a-1714-4fdd-b5aa-1e27caa4be43
-- title:
--   Theorem 16 — Beigi–Taghavi with subroutine calls: a dual of cost $O(T\sqrt{qG})$ and $Q_{1/3}(f)=O(T\sqrt{qG})$
-- statement:
--   Let $D\subseteq\Sigma^n$ be a promise set, $f:D\to O$, and for $j$ in a finite set $J$ let $g_j:D\to\Gamma_j$ be functions with $\mathrm{ADV}^\pm(g_j)\le T$ for some $T\ge0$; all alphabets are finite. Suppose a deterministic call procedure computes $f(x)$ for every $x\in D$, accessing $x$ only through calls to the $g_j$: the next call may depend on earlier answers, each call designates at most one outgoing branch as predicted, and answers may be grouped into one branch. Suppose every execution on $x\in D$ makes at most $q$ calls and takes an unpredicted branch at most $G$ times ($q,G\in\mathbb N$). Then, with a universal constant $C$:
--
--   1. $f$ has an all-pairs dual of cost at most $C\,T\sqrt{qG}$, and
--   $$Q_{1/3}(f)\le C\,T\sqrt{qG};$$
--   2. if $q=0$, $G=0$ or $T=0$, then $f$ is constant on $D$, has a dual of cost $0$, and $Q_{1/3}(f)=0$.
--
--   The called functions may read overlapping input positions. The theorem charges each call according to the adversary bound of the subroutine and each unpredicted branch once, and is the composition tool behind the stably ordered algorithms of Section 7.
--
--   **Formalization Note** The procedure is the tree type `CallTree`, and its execution returns the output, the number of calls and the number of unpredicted branches. $\mathrm{ADV}^\pm$, the all-pairs dual (Eq. (3)) and its cost (Eq. (4)) are the published definitions of the base mission.
--
--   Differences from the source:
--
--   - generalization: input positions [n] (D ⊆ Σⁿ) → any finite nonempty type I of positions; reason: specializes to I = Fin n
--   - encoding: n ≥ 1 and O nonempty (implicit) → [Nonempty I], [Nonempty O]; reason: with no position the platform's query register is empty and Q_{1/3} = ⊤; an empty O forces D = ∅, an undefined case
--   - encoding: a deterministic adaptive procedure with predictions and grouped branches → a finite tree (CallTree) with branches numbered 0, …, k−1 and an optional predicted branch per call; reason: any procedure is equivalent on D to such a tree (prune unreachable parts below depth q)
--   - encoding: O(T√(qG)) for the dual and for Q_{1/3} → one universal C > 0 for both, chosen before all types; reason: an O-bound with a universal constant
--   - encoding: the cost is zero → there is a dual of cost 0 and Q_{1/3}(f) = 0; reason: the two costs named in the theorem
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 16 (Beigi–Taghavi with subroutine calls), p.31

import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_DualFeasible
import Definitions.Def_MonoidProdQ_dualCost
import Definitions.Def_MonoidProdQ_Supplement_CallTree_run

open scoped ENNReal

universe u v w x y

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 16 (Beigi–Taghavi with subroutine
calls), p.31: "Let f : D → O, where D ⊆ Σⁿ, and let g_j : D → Γ_j, for j in a finite index set J,
be functions with ADV±(g_j) ≤ T for some T ≥ 0. All input and output alphabets are finite.
Suppose a deterministic procedure computes f(x), accessing x only through calls to the functions
g_j. … Suppose every execution on x ∈ D makes at most q calls and takes an unpredicted branch at
most G times, where q, G are nonnegative integers. Then f has a dual of cost O(T√(qG)), and
Q_{1/3}(f) = O(T√(qG)). The called functions may depend on overlapping input positions. If
q = 0, G = 0, or T = 0, then f is constant and the cost is zero." Two conjuncts:

1. one universal `C > 0` such that, under these hypotheses, `f` has an all-pairs dual
   (`DualFeasible`) of cost (`dualCost`) at most `C·T·√(qG)` and `Q_{1/3}(f) ≤ C·T·√(qG)`;
2. if `q = 0`, `G = 0` or `T = 0`, then `f` is constant on `D`, has a dual of cost `0`, and
   `Q_{1/3}(f) = 0`.

**Formalization Note.** The procedure is a `CallTree` and its execution `CallTree.run` returns
(output, calls, unpredicted branches); the bounds `q`, `G` hold on every execution from `D`. The
`g_j` are arbitrary functions of the whole input (they may read overlapping positions), and
`ADV±(g_j)` is `advPm (g j) D` on the same promise domain. The index set `I` of input positions
is nonempty (`n ≥ 1`) and `O` is nonempty (`f` takes values); with no index the platform's query
register is empty. -/
theorem theorem_16 :
    (∃ C : ℝ, 0 < C ∧
      ∀ (I : Type u) (Sig : Type v) (O : Type w) (J : Type x) (Γ : J → Type y)
        [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Sig] [DecidableEq Sig] [Fintype O]
        [DecidableEq O] [Nonempty O] [Fintype J] [∀ j, Fintype (Γ j)] [∀ j, DecidableEq (Γ j)]
        (f : (I → Sig) → O) (D : Finset (I → Sig)) (g : ∀ j, (I → Sig) → Γ j) (T : ℝ)
        (q G : ℕ) (P : CallTree J Γ O),
        0 ≤ T → (∀ j, advPm (g j) D ≤ ENNReal.ofReal T) →
        (∀ x ∈ D, (P.run g x).1 = f x) → (∀ x ∈ D, (P.run g x).2.1 ≤ q) →
        (∀ x ∈ D, (P.run g x).2.2 ≤ G) →
        (∃ (d : ℕ) (u v : D → I → EuclideanSpace ℂ (Fin d)),
          DualFeasible f D u v ∧ (dualCost u v : ℝ) ≤ C * T * Real.sqrt (q * G)) ∧
        (Q13 f D : ℝ≥0∞) ≤ ENNReal.ofReal (C * T * Real.sqrt (q * G))) ∧
    (∀ (I : Type u) (Sig : Type v) (O : Type w) (J : Type x) (Γ : J → Type y)
        [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Sig] [DecidableEq Sig] [Fintype O]
        [DecidableEq O] [Nonempty O] [Fintype J] [∀ j, Fintype (Γ j)] [∀ j, DecidableEq (Γ j)]
        (f : (I → Sig) → O) (D : Finset (I → Sig)) (g : ∀ j, (I → Sig) → Γ j) (T : ℝ)
        (q G : ℕ) (P : CallTree J Γ O),
        0 ≤ T → (∀ j, advPm (g j) D ≤ ENNReal.ofReal T) →
        (∀ x ∈ D, (P.run g x).1 = f x) → (∀ x ∈ D, (P.run g x).2.1 ≤ q) →
        (∀ x ∈ D, (P.run g x).2.2 ≤ G) → (q = 0 ∨ G = 0 ∨ T = 0) →
        (∀ x ∈ D, ∀ y ∈ D, f x = f y) ∧
        (∃ (d : ℕ) (u v : D → I → EuclideanSpace ℂ (Fin d)),
          DualFeasible f D u v ∧ dualCost u v = 0) ∧
        Q13 f D = 0) := by sorry

end MonoidProdQ.Supplement
