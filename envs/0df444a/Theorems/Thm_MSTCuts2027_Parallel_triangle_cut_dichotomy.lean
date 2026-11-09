-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_triangle_cut_dichotomy
-- name    : MSTCuts2027.Parallel.triangle_cut_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:25.538198+00:00
-- url     : https://prove2.me/theorems/88afece8-bd5f-48f7-9834-8ce392efbcf8
-- title:
--   Lemma 4 — the triangle dichotomy for mincuts
-- statement:
--   Let $F$ be a symmetric real cut function, $u,v,x$ three vertices, and $C$ a $(u,v)$-mincut that keeps $x$ on the side of $u$. Then exactly one of the following holds:
--
--   1. $\lambda_1(x,v)=\lambda_1(u,v)$, and $C$ is an $(x,v)$-mincut;
--   2. $\lambda_1(x,v)<\lambda_1(u,v)$, and any cut is an $(x,v)$-mincut if and only if it is an $(x,u)$-mincut.
--
--   This is the fact behind EliminateTriangle: one known cut decides which edge of a triangle of $G_1$ can be discarded.
--
--   Differences from the source:
--   - encoding: three vertices, C keeps x on the side of u → x ≠ u, x ≠ v, and (x ∈ C ↔ u ∈ C); reason: x ≠ v follows anyway, and x = u is not a triangle; the cut (C, V∖C) is unoriented, so "side" is membership agreement
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 4, printed p. 6, PDF p. 8

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel

namespace MSTCuts2027.Parallel

/-- Lemma 4: exactly one of the two assertions holds. -/
theorem triangle_cut_dichotomy {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) (hF : IsSymmetricCutFunction F)
    (u v x : V) (hxu : x ≠ u) (hxv : x ≠ v) (C : Finset V) (hC : IsMincut F u v C)
    (hside : x ∈ C ↔ u ∈ C) :
    Xor (lam F x v = lam F u v ∧ IsMincut F x v C)
      (lam F x v < lam F u v ∧ ∀ D : Finset V, IsMincut F x v D ↔ IsMincut F x u D) := by sorry

end MSTCuts2027.Parallel
