-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_Supplement_second_mincut_type2
-- name    : MSTCuts2027.Parallel.Supplement.second_mincut_type2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:38:20.43837+00:00
-- url     : https://prove2.me/theorems/1c5f2bb3-517a-45b0-a314-a9f53930b7a6
-- title:
--   Lemma 8 — Type 2 triangles for second mincuts
-- statement:
--   Let $F$ be a symmetric real cut function on a finite vertex set $V$, and let $u,v,x$ be vertices with $x\notin\{u,v\}$. Suppose
--   $$\lambda_1(u,v)=\lambda_1(x,u)=\lambda_1(x,v),$$
--   and let $C$ be any second $(u,v)$-mincut that keeps $x$ on the side of $u$. Then exactly one of the following holds.
--
--   1. $\lambda_2(x,v)=\lambda_2(u,v)$, and $C$ is a second $(x,v)$-mincut.
--   2. $\lambda_2(x,v)<\lambda_2(u,v)$, and a cut is a second $(x,v)$-mincut if and only if it is a second $(x,u)$-mincut.
--
--   This is the Type 2 counterpart of Lemma 7: when the three mincut values coincide, the stored second $(u,v)$-mincut decides which edge at $x$ can be dropped.
--
--   Differences from the source:
--   - encoding: C keeps x on the side of u → x ∈ C ↔ u ∈ C; reason: the cut (C, V∖C) is unoriented
--   - encoding: exactly one of the assertions holds → Xor of the two assertions; reason: same statement
--   - encoding: the three vertices of a triangle → hypotheses x ≠ u, x ≠ v (u ≠ v follows from C separating them); reason: λ1 is defined only on pairs of distinct vertices
--   - generalization: standing assumption that every pair has a second mincut → not assumed; reason: C is a second (u,v)-mincut and separates x,v with value strictly above their common minimum, so finiteness supplies a second (x,v)-mincut (not necessarily C); no λ2(x,u) is evaluated, and in the second branch an optimal (x,v)-cut also supplies existence for (x,u); the source statement is the special case with the assumption
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 8, printed p. 12, PDF p. 14

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel

namespace MSTCuts2027.Parallel.Supplement

open MSTCuts2027.Parallel

/-- Lemma 8 (Type 2): exactly one of the two assertions holds. -/
theorem second_mincut_type2 {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) (hF : IsSymmetricCutFunction F)
    (u v x : V) (hxu : x ≠ u) (hxv : x ≠ v)
    (h₁ : lam F u v = lam F x u) (h₂ : lam F x u = lam F x v)
    (C : Finset V) (hC : IsSecondMincut F u v C) (hside : x ∈ C ↔ u ∈ C) :
    Xor (lam2 F x v = lam2 F u v ∧ IsSecondMincut F x v C)
      (lam2 F x v < lam2 F u v ∧
        ∀ D : Finset V, IsSecondMincut F x v D ↔ IsSecondMincut F x u D) := by sorry

end MSTCuts2027.Parallel.Supplement
