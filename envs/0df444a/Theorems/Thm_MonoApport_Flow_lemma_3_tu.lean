-- Prove2me | Theorems.Thm_MonoApport_Flow_lemma_3_tu
-- name    : MonoApport.Flow.lemma_3_tu
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:37.901282+00:00
-- url     : https://prove2.me/theorems/8c984731-e722-4810-a991-947dd0e7681d
-- title:
--   Proof of Lemma 3, §C.3, p. 40 — the matrix with rows e_{i,t}, −e_{i,t}, e′_t, −e′_t is totally unimodular
-- statement:
--   Fix $n$ states and $L$ seats, and index coordinates by pairs $(j,\ell)\in[n]\times[L]$ (the variable $x(j,\ell)$). For $i\in[n]$ and $t\in[L]$ let $e_{i,t}$ be the 0/1 vector with $(e_{i,t})_{(j,\ell)}=1$ exactly when $j=i$ and $\ell\le t$ (the prefix sum of state $i$ up to seat $t$), and $e'_t$ the 0/1 vector with $(e'_t)_{(j,\ell)}=1$ exactly when $\ell=t$ (the column of seat $t$). Let $M$ be the integer matrix whose rows are
--   $$e_{i,t},\quad -e_{i,t}\quad(i\in[n],\,t\in[L]),\qquad e'_t,\quad -e'_t\quad(t\in[L]).$$
--
--   **Claim (proof of Lemma 3).** $M$ is totally unimodular: every square submatrix has determinant $0$, $1$ or $-1$.
--
--   These are the constraint rows of the linear program (1)-(4) in the form $Mz\le b$; total unimodularity is the step from which the paper derives the integrality of (1)-(4) (Lemma 3).
--
--   **Formalization Note.** Rows are indexed by the disjoint sum $([n]\times[L])\sqcup([n]\times[L])\sqcup[L]\sqcup[L]$ and columns by $[n]\times[L]$, instead of $[2(n+1)L]$ and $[nL]$ with the paper's ordering; total unimodularity is invariant under such relabellings. Mathlib's `Matrix.IsTotallyUnimodular` is used.
--
--   Differences from the source:
--   - generalization: an instance (p, H) ∈ ℕⁿ × ℕ, so n ≥ 1 and H ≥ 1 seats → every n, L : ℕ, including 0; reason: the matrix does not depend on p, and for n = 0 or L = 0 it has no columns or no rows; the statement specializes to the source's at n ≥ 1, L = H ≥ 1
--   - encoding: rows indexed by k ∈ [2(n + 1)H] in the order e_{i,t}, −e_{i,t}, e′_t, −e′_t, columns by j ∈ [nH] listing x(1,1), …, x(n,H) → rows indexed by a sum type (Fin n × Fin L) ⊕ (Fin n × Fin L) ⊕ Fin L ⊕ Fin L, columns by Fin n × Fin L, with 0-indexed seats; reason: a relabelling of rows and columns; total unimodularity is invariant under it
-- source:
--   Cembrano, Correa, Schmidt-Kraepelin, Tsigonias-Dimitriadis & Verdugo, New Combinatorial Insights for Monotone Apportionment, arXiv:2410.23869v1, proof of Lemma 3, §C.3, pp. 39–40

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

namespace MonoApport.Flow

/-- Proof of Lemma 3 (§C.3, p. 40): the matrix with rows `e_{i,t}`, `−e_{i,t}`, `e′_t`, `−e′_t`
is totally unimodular. -/
theorem lemma_3_tu (n L : ℕ) : (constraintMatrix n L).IsTotallyUnimodular := by sorry

end MonoApport.Flow
