-- Prove2me | Theorems.Thm_LittleCharity_EFX_lemma_6
-- name    : LittleCharity.EFX.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:43.31598+00:00
-- url     : https://prove2.me/theorems/10bef373-2315-47ef-92af-7c10b42f77a7
-- title:
--   Lemma 6 — enough pool goods force a U2 cycle
-- statement:
--   Let $n\ge1$, and let $X$ be an EFX allocation under monotone valuations whose envy graph $G_X$ is acyclic. Suppose Rule $U_0$ is not applicable and the pool has at least as many goods as $G_X$ has sources, $|P|\ge\#\mathrm{sources}(G_X)$. Then there are $\ell\ge1$, distinct goods $g_0,\dots,g_{\ell-1}\in P$, distinct sources $s_0,\dots,s_{\ell-1}$ of $G_X$ and distinct agents $t_0,\dots,t_{\ell-1}$ (indices modulo $\ell$, so $t_\ell=t_0$) such that for every $a$:
--
--   1. $t_a\in C(s_a)$, i.e. $t_a$ is reachable from $s_a$ in $G_X$;
--   2. $t_{a+1}$ is a most envious agent of $X_{s_a}\cup\{g_a\}$;
--
--   and moreover the ordering property holds:
--   $$
--   a<b\ \Longrightarrow\ t_b\notin C(s_a)\qquad(0\le a<b\le\ell-1).
--   $$
--
--   These are exactly the data that make Rule $U_2$ applicable; the ordering property keeps the envy paths used by $U_2$ vertex-disjoint.
--
--   **Formalization Note** Three disclosed changes. (i) The page assumes $|P|\ge n$; the Lean hypothesis $|P|\ge\#\mathrm{sources}$ is weaker (there are at most $n$ sources), it is what the proof uses (one fresh good per source), and it is what Theorem 8's bound $|P|<\#\mathrm{sources}$ needs, so the Lean statement implies the printed one. (ii) EFX and acyclicity of $G_X$ are Algorithm 1's invariant; without acyclicity an agent need not lie in any $C(s)$. (iii) The ordering property is proved in the page's proof (the agents $t_k\notin C(s_0)\cup\cdots\cup C(s_{k-1})$, footnote 8) and is added to the conclusion. The page's list "$t_1,t_1,\dots,t_\ell$" is a typo for $t_1,\dots,t_\ell$; the page's pairing ($t_i$ most envious of $X_{s_{i-1}}\cup g_{i-1}$) is item 2 above. Indices are $0$-based; "$+1$ modulo $\ell$" is `finRotate ℓ`. The hypothesis $n\ge1$ is added (the paper always has agents).
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 10–11, Lemma 6 and proof

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.EFX

theorem lemma_6 {n m : ℕ} (hn : 0 < n)
    (v : Fin n → Finset (Fin m) → ℝ) (hmono : IsMonotoneVal v)
    (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (hEFX : IsEFX v X)
    (hacyc : EnvyAcyclic v X) (hU0 : ¬ U0Applicable v X)
    (hP : (sources v X).card ≤ (pool X).card) :
    ∃ ℓ : ℕ, 0 < ℓ ∧
      ∃ (s : Fin ℓ → Fin n) (g : Fin ℓ → Fin m) (t : Fin ℓ → Fin n),
        Function.Injective s ∧ Function.Injective g ∧ Function.Injective t ∧
        (∀ a, g a ∈ pool X) ∧ (∀ a, IsSource v X (s a)) ∧
        (∀ a, Reach v X (s a) (t a)) ∧
        (∀ a, IsMostEnviousAgent v X (insert (g a) (X (s a)))
          (t (finRotate ℓ a))) ∧
        (∀ a b, a < b → ¬ Reach v X (s a) (t b)) := by sorry
end LittleCharity.EFX
