-- Prove2me | Theorems.Thm_LSWCuttingPlane_SFMArcs_restriction_claim
-- name    : LSWCuttingPlane.SFMArcs.restriction_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:45.155318+00:00
-- url     : https://prove2.me/theorems/dfc9b3f8-f61c-4552-8015-baee1fef10a7
-- title:
--   Proof of Lemma 79, p. 85 — f′(S) = f(S ∪ R(p)) is submodular, S_min ∖ R(p) minimizes it, y′ restricted lies in B(f′)
-- statement:
--   Let $f : 2^V \to \mathbb Z$ be submodular with $f(\emptyset) = 0$, let $A$ be an acyclic set of arcs, and let $y = \sum_k \lambda^{(k)} y^{(k)}$ be a convex combination of BFS's consistent with $A$, with defining permutations $\sigma_k$. Fix $p \in V$, write $V' = V \setminus R(p)$, and let $y' = \sum_k \lambda^{(k)} y'^{(k)}$, where $y'^{(k)}$ is the BFS of the permutation $\tau_k$ obtained from $\sigma_k$ by moving $R(p)$ to the front. Define $f'(S) = f(S \cup R(p))$ for $S \subseteq V'$. Suppose $S_{\min}$ is a minimizer of $f$ over the ring family $\mathcal F_A$ and $p \in S_{\min}$. Then:
--
--   1. $R(p) \subseteq S_{\min}$;
--   2. $f'$ is submodular on $V'$: $f'(T + i) - f'(T) \le f'(S + i) - f'(S)$ for $S \subseteq T \subseteq V'$ and $i \in V' \setminus T$;
--   3. $S_{\min} \setminus R(p)$ minimizes $f'$ over the corresponding ring family $\{S \subseteq V' : S \cup R(p) \in \mathcal F_A\}$;
--   4. the restriction of $y'$ to $V'$ lies in the base polyhedron of $f' - f'(\emptyset)$:
--   $$y'(S) \le f(S \cup R(p)) - f(R(p)) \quad (S \subseteq V'), \qquad y'(V') = f(V) - f(R(p)).$$
--
--   This reduces the search for the new arc to an application of Lemma 77 to $f'$ on the smaller ground set $V'$.
--
--   **Formalization Note** The paper writes "$\vec y'_{V\setminus R(p)}$ is a convex combination of the BFS's of the base polyhedron $\mathcal B(f')$". Since §13.1 normalizes every function to vanish at $\emptyset$ and $\mathcal B(f')$ only makes sense for the normalized function, item 4 uses $f' - f'(\emptyset) = f(\cdot \cup R(p)) - f(R(p))$, and it states membership in the base polyhedron (what the proof uses) rather than the convex-combination form. The sets $S \subseteq V'$ are subsets of `Fin n` contained in $V'$, and $f'$ is written out as $f(\cdot \cup R(p))$.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 85, proof of Lemma 79, second paragraph

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

namespace LSWCuttingPlane.SFMArcs

open Finset

/-- Proof of Lemma 79, p. 85, the function `f′(S) = f(S ∪ R(p))` for `S ⊆ V′ = V \ R(p)`:
(a) if `p` is in a minimizer `S_min` of `f` over the ring family of `A`, then `R(p) ⊆ S_min`;
(b) `f′` satisfies Definition 58 on the ground set `V′`, and `S_min \ R(p)` minimizes `f′` over
the corresponding ring family `{S ⊆ V′ : S ∪ R(p) ∈ F}`;
(c) the vector `y′ = ∑_k λ^{(k)} y′^{(k)}`, where `y′^{(k)}` is the BFS whose defining permutation
is that of `y^{(k)}` with `R(p)` moved to the front, restricted to `V′`, lies in the base
polyhedron of the normalized function `f′ − f′(∅)`. -/
theorem restriction_claim {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hf0 : f ∅ = 0)
    (A : Fin n → Fin n → Prop) (hA : Acyclic A)
    {ι : Type} [Fintype ι] (lam : ι → ℝ) (σs τs : ι → Equiv.Perm (Fin n))
    (hcomb : IsConsistentComb A lam σs) (p : Fin n)
    (hτ : ∀ k, IsFrontload (σs k) (R A p) (τs k))
    (Smin : Finset (Fin n)) (hmin : IsMinimizer A f Smin) (hp : p ∈ Smin) :
    -- (a)
    R A p ⊆ Smin ∧
    -- (b) `f′` is submodular on the ground set `V′`
    (∀ (S T : Finset (Fin n)) (i : Fin n), S ⊆ T → T ⊆ Finset.univ \ R A p →
        i ∈ Finset.univ \ R A p → i ∉ T →
        f (insert i T ∪ R A p) - f (T ∪ R A p) ≤ f (insert i S ∪ R A p) - f (S ∪ R A p)) ∧
    -- (b) `S_min \ R(p)` minimizes `f′` over the corresponding ring family
    ((Smin \ R A p) ∪ R A p ∈ ringFamily A ∧
      ∀ S : Finset (Fin n), S ⊆ Finset.univ \ R A p → S ∪ R A p ∈ ringFamily A →
        f ((Smin \ R A p) ∪ R A p) ≤ f (S ∪ R A p)) ∧
    -- (c) `y′` restricted to `V′` lies in `B(f′ − f′(∅))`
    ((∀ S : Finset (Fin n), S ⊆ Finset.univ \ R A p →
        ysum (combo f lam τs) S ≤ ((f (S ∪ R A p) - f (R A p) : ℤ) : ℝ)) ∧
      ysum (combo f lam τs) (Finset.univ \ R A p) =
        ((f (Finset.univ \ R A p ∪ R A p) - f (R A p) : ℤ) : ℝ)) := by sorry

end LSWCuttingPlane.SFMArcs
