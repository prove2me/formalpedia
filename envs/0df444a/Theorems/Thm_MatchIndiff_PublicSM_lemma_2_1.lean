-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_2_1
-- name    : MatchIndiff.PublicSM.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:37.941005+00:00
-- url     : https://prove2.me/theorems/d00cfcfa-a762-4b4a-9579-0c6db222c030
-- title:
--   Lemma 2.1 — accepted profiles of a fixed board form a product, and a row and board fix the decoded component
-- statement:
--   Fix a verification protocol at a fixed public input, with report holders $v\in V$, allowed report sets $T_v$, board alphabet $C$, decoders $D_v$ and checks $V_v$, and fix a board $c\in C$. Put $S_v(c)=\{x\in T_v: V_v(x,c)=1\}$. Then the profiles $P\in\prod_v T_v$ on which all checks accept $c$ form exactly the product
--   $$\{P\in\textstyle\prod_v T_v:\ \forall v,\ V_v(P_v,c)=1\}=\prod_{v\in V}S_v(c),$$
--   and a fixed row and board give the same decoded component: if $P_v=P'_v$ then $D_v(P_v,c)=D_v(P'_v,c)$.
--
--   This rectangle property is what makes the fooling-set lower bound of Theorem 6.2 work: rows copied from two accepted profiles form a mixed profile on which the same board is still accepted.
--
--   **Formalization Note.** Stated for the generic `VerifProtocol R X C` with an arbitrary holder type `V`, report types `R v`, domains `T v : Set (R v)` and any board type `C`.
--
--   Differences from the source:
--   - generalization: a protocol of one of the paper's models: finite report sets T_v, finite holder set V, finite nonempty board alphabet C → any holder type V, any report types R v with domains T v, any board type C, any output types; reason: the statement and its proof use no finiteness; it specializes to the paper's protocols
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 7, Lemma 2.1

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Protocol

namespace MatchIndiff.PublicSM

/-- Lemma 2.1 (p. 7): for a fixed board `c`, the profiles of the product domain `∏ T_v` on which
all checks accept `c` form exactly `∏_v S_v(c)`, `S_v(c) = {x ∈ T_v : V_v(x, c) = 1}`; and a fixed
row and board give the same decoded component. -/
theorem lemma_2_1 {V : Type*} {R X : V → Type*} {C : Type*} (p : VerifProtocol R X C)
    (T : (v : V) → Set (R v)) (c : C) :
    {P : (v : V) → R v | (∀ v, P v ∈ T v) ∧ ∀ v, p.chk v (P v) c = true} =
        Set.pi Set.univ (fun v => {x : R v | x ∈ T v ∧ p.chk v x c = true}) ∧
      ∀ (P P' : (v : V) → R v) (v : V), P v = P' v → p.dec v (P v) c = p.dec v (P' v) c := by sorry

end MatchIndiff.PublicSM
