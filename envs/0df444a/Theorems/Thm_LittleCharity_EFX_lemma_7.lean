-- Prove2me | Theorems.Thm_LittleCharity_EFX_lemma_7
-- name    : LittleCharity.EFX.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:59.038648+00:00
-- url     : https://prove2.me/theorems/615bca79-9d43-4569-9f05-19955d5b997d
-- title:
--   Lemma 7 — Rule U2 increases welfare and preserves EFX
-- statement:
--   Let $X$ be an EFX allocation under monotone valuations. Suppose Rule $U_2$'s precondition holds with the ordering property of Lemma 6: there are $\ell\ge1$, distinct goods $g_0,\dots,g_{\ell-1}\in P(X)$, distinct sources $s_0,\dots,s_{\ell-1}$ and distinct agents $t_0,\dots,t_{\ell-1}$ (indices modulo $\ell$) with $t_a\in C(s_a)$ and $t_b\notin C(s_a)$ for $a<b$. For each $a$ let $Z_a$ be an inclusion-wise minimal envied subset of $X_{s_a}\cup\{g_a\}$ with $v_{t_{a+1}}(Z_a)>v_{t_{a+1}}(X_{t_{a+1}})$ (line 12), and let $s_a=u^a_0\to u^a_1\to\cdots\to u^a_{m_a}=t_a$ be a path of distinct agents in $G_X$. Let $X'$ be the allocation of lines 15–17:
--   $$
--   X'_{u^a_k}=X_{u^a_{k+1}}\ (0\le k<m_a),\qquad X'_{t_{a+1}}=Z_a,\qquad X'_j=X_j\ \text{otherwise}.
--   $$
--   Then $X'$ is an allocation, it is EFX, $\phi(X')>\phi(X)$, and its pool is
--   $$
--   P(X')=\Bigl(P(X)\setminus\{g_0,\dots,g_{\ell-1}\}\Bigr)\ \cup\ \bigcup_{a=0}^{\ell-1}\Bigl(\bigl(X_{s_a}\cup\{g_a\}\bigr)\setminus Z_a\Bigr).
--   $$
--
--   Rule $U_2$ is the step that makes progress when neither $U_0$ nor $U_1$ applies.
--
--   **Formalization Note** $X'$ is the explicit allocation `u2Allocation` built from the paths, the terminal agents and the sets $Z_a$, not an arbitrary allocation. The ordering property (proved inside Lemma 6) is added as a hypothesis: with only $t_a\in C(s_a)$, as printed in $U_2$'s precondition, two paths may share an agent, who would then be assigned two bundles. The pool formula corrects Algorithm 2, line 13, which prints a malformed expression with an out-of-range $g_\ell$. Paths are lists with first element $s_a$, last element $t_a$, consecutive envy edges and no repeated agent.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 9, 11, Algorithm 2 Rule U2, Lemma 7

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.EFX

theorem lemma_7 {n m ℓ : ℕ} (hℓ : 0 < ℓ)
    (v : Fin n → Finset (Fin m) → ℝ) (hmono : IsMonotoneVal v)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (hEFX : IsEFX v X)
    (s : Fin ℓ → Fin n) (g : Fin ℓ → Fin m) (t : Fin ℓ → Fin n)
    (hs : Function.Injective s) (hg : Function.Injective g)
    (ht : Function.Injective t)
    (hgP : ∀ a, g a ∈ pool X)
    (hsSource : ∀ a, IsSource v X (s a))
    (htReach : ∀ a, Reach v X (s a) (t a))
    (htOrder : ∀ a b, a < b → ¬ Reach v X (s a) (t b))
    (Z : Fin ℓ → Finset (Fin m))
    (hZ : ∀ a, IsMinimalEnviedSubset v X (insert (g a) (X (s a))) (Z a))
    (htZ : ∀ a, v (t (finRotate ℓ a)) (X (t (finRotate ℓ a))) <
      v (t (finRotate ℓ a)) (Z a))
    (p : Fin ℓ → List (Fin n))
    (hpHead : ∀ a, (p a).head? = some (s a))
    (hpLast : ∀ a, (p a).getLast? = some (t a))
    (hpChain : ∀ a, (p a).IsChain (Envies v X))
    (hpNodup : ∀ a, (p a).Nodup) :
    let X' := u2Allocation X t Z p
    IsPartialAllocation X' ∧ IsEFX v X' ∧
    welfare v X < welfare v X' ∧
    pool X' = (pool X \ Finset.univ.image g) ∪
      Finset.univ.biUnion (fun a => insert (g a) (X (s a)) \ Z a) := by sorry
end LittleCharity.EFX
