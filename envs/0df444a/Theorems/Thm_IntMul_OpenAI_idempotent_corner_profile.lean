-- Prove2me | Theorems.Thm_IntMul_OpenAI_idempotent_corner_profile
-- name    : IntMul.OpenAI.idempotent_corner_profile
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:32:24.844726+00:00
-- url     : https://prove2.me/theorems/cae2f330-1991-460c-a3df-b7ef2b9deac0
-- title:
--   Bruhat profile of an idempotent with invertible corner
-- statement:
--   Let $K$ be a field, $m,k\in\mathbb N$ with $2k\le m$, and split the coordinates into $L=[0,k)$, $M=[k,m-k)$, $R=[m-k,m)$. Let $p$ be an $m\times m$ idempotent of rank $m-k$ whose corner $C=p[L,R]$ is invertible. Then for every northeast block (rows $<X$, columns $\ge Y$),
--   $$\operatorname{rank}p[{<}X,{\ge}Y]=\operatorname{rank}C[{<}X,\ {\ge}Y]\;+\;\#\{i\in M:\ Y\le i<X\},$$
--   where the rows of $C$ are indexed by $L$ and its columns by $R$ (so column $r$ of $C$ is column $m-k+r$ of $p$).
--
--   Combined with `IntMul.OpenAI.bruhat_rank_profile` and `IntMul.OpenAI.partial_perm_eq_of_corner_counts`, this says the Bruhat pivots of $p$ are the pivots of $C$ on $L\times R$ together with the diagonal of $M$. With `IntMul.OpenAI.partial_swap_corner_ranks` this gives the *partial-swap batching lemma* of Jain's notes. An edge frame $S_p$ with $\operatorname{rank}p=a>m/2$ compiles into $m-a$ corner transpositions $H_l\leftrightarrow D_{\sigma(l)}$ plus one aligned run $H_i\leftrightarrow D_i$, $i\in M$, of width $2a-m$, which is a single batched interchange call.
--
--   **Formalization Note** Rows $<X$ and columns $\ge Y$ use subtypes of `Fin m` with natural-number bounds; $C$ is a `submatrix` of $p$.
-- source:
--   S. Jain, integer-mult-kappa, notes/partial-swap-batching.tex (Lemma 'Partial-swap factorization', H rows against D columns), https://github.com/Swapnil-jain/integer-mult-kappa

import Mathlib

namespace IntMul.OpenAI

theorem idempotent_corner_profile {m k : ℕ} {K : Type*} [Field K] (hk : 2 * k ≤ m)
    (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p) (hrank : p.rank = m - k)
    (hC : (p.submatrix (fun l : Fin k => (⟨l.val, by omega⟩ : Fin m))
        (fun r : Fin k => (⟨m - k + r.val, by omega⟩ : Fin m))).det ≠ 0)
    (X Y : ℕ) :
    (p.submatrix (fun r : {r : Fin m // r.val < X} => r.1) (fun c : {c : Fin m // Y ≤ c.val} => c.1)).rank =
      ((p.submatrix (fun l : Fin k => (⟨l.val, by omega⟩ : Fin m))
          (fun r : Fin k => (⟨m - k + r.val, by omega⟩ : Fin m))).submatrix
          (fun l : {l : Fin k // l.val < X} => l.1) (fun r : {r : Fin k // Y ≤ m - k + r.val} => r.1)).rank +
      (Finset.univ.filter fun i : Fin m => k ≤ i.val ∧ i.val < m - k ∧ Y ≤ i.val ∧ i.val < X).card := by sorry

end IntMul.OpenAI
